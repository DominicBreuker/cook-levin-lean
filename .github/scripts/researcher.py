#!/usr/bin/env python3
"""
Researcher Agent for the P vs NP Research Project.

This script is designed for the real Mistral Vibe CLI in CI. The repository
also ships a mock CLI for local development/tests of researcher.py so we can
exercise the wrapper logic without consuming a live API key.

Required environment variable:
    MISTRAL_VIBE_KEY or MISTRAL_API_KEY  — Mistral API key

Optional environment variables:
    MISTRAL_MODEL            — Mistral model name
    MISTRAL_MAX_TURNS        — Max Vibe turns (default: 12)
    MISTRAL_MAX_PRICE        — Max Vibe price in dollars
    MISTRAL_TIMEOUT_SECONDS  — Timeout for the Vibe run (default: 1800)
    MISTRAL_VIBE_BIN         — Override path to the `vibe` executable
    MISTRAL_VIBE_SESSION_ID  — Explicit Vibe session ID used for resume demo

Command-line arguments:
    --run-count               — Number of Vibe passes to run (default: 2)
    --overall-timeout-minutes — Stop starting new passes once cumulative
                                runtime reaches this limit (default: 0, disabled)
"""

from __future__ import annotations

import argparse
import json
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT: Path = Path(__file__).resolve().parent.parent.parent
PROMPT_TEMPLATE_PATH: Path = REPO_ROOT / ".github" / "prompts" / "researcher_vibe.md"
MOCK_VIBE_PATH: Path = REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"
PROMPT_FILENAME = ".mistral-researcher-prompt.md"
# Status detection only inspects the normalized leading status marker, not
# later prose such as "Task 6 complete; Task 7 in progress".
DEAD_STATUS_HEADS: set[str] = {"dead end", "archived", "retired"}
# Matched case-insensitively against normalized_status_head(...) to treat
# solved/frozen tracks as ineligible researcher targets even if they still
# carry a stale positive priority.
SOLVED_STATUS_HEAD_PREFIXES: tuple[str, ...] = (
    "complete",
    "completed",
    "solved",
    "proven",
    "finished",
    "frozen",
    "closed",
)
TARGET_TABLE_BASE_HEADERS = ("problem", "approach", "priority", "status")
TARGET_TABLE_HEADERS = {TARGET_TABLE_BASE_HEADERS, TARGET_TABLE_BASE_HEADERS + ("relationships",)}
PRIORITY_PATTERN = re.compile(r"[0-9]+(?:\.[0-9]+)?")
SESSION_METADATA_FILENAME = "meta.json"
SESSION_MESSAGES_FILENAME = "messages.jsonl"
# Vibe emits single-line tagged status messages such as
# `<vibe_stop_event>Turn limit reached</vibe_stop_event>`.
VIBE_TAG_PATTERN = re.compile(r"^<(?P<tag>[a-z_]+)>(?P<message>.*)</(?P=tag)>$")
MISTRAL_MODEL: str = os.environ.get("MISTRAL_MODEL", "").strip()
MISTRAL_AGENT: str = os.environ.get("MISTRAL_AGENT", "auto-approve").strip()
MISTRAL_MAX_TURNS: str = os.environ.get("MISTRAL_MAX_TURNS", "").strip()
MISTRAL_MAX_PRICE: str = os.environ.get("MISTRAL_MAX_PRICE", "").strip()
MISTRAL_TIMEOUT_SECONDS: int = int(os.environ.get("MISTRAL_TIMEOUT_SECONDS", "3600"))
MISTRAL_VIBE_SESSION_ID: str = os.environ.get("MISTRAL_VIBE_SESSION_ID", "").strip()


def get_mistral_api_key() -> str:
    """Return the configured API key, preferring the researcher-specific variable."""
    if "MISTRAL_VIBE_KEY" in os.environ:
        return os.environ.get("MISTRAL_VIBE_KEY", "").strip()
    return os.environ.get("MISTRAL_API_KEY", "").strip()


MISTRAL_API_KEY: str = get_mistral_api_key()


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def non_negative_float(value: str) -> float:
    parsed = float(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be non-negative")
    return parsed


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run the P vs NP researcher agent.")
    parser.add_argument(
        "--run-count",
        type=int,
        default=2,
        help="number of Vibe passes to execute (default: 2)",
    )
    parser.add_argument(
        "--overall-timeout-minutes",
        type=non_negative_float,
        default=0.0,
        help=(
            "stop starting new Vibe passes once cumulative runtime reaches this many minutes; "
            "0 disables the limit"
        ),
    )
    parser.add_argument(
        "--prompt",
        type=str,
        default=None,
        help="custom prompt passed to Vibe CLI",
    )
    parser.add_argument(
        "--delay",
        type=positive_int,
        default=1,
        help="time in seconds to wait between runs of vibe CLI",
    )
    return parser.parse_args(argv)


# ---------------------------------------------------------------------------
# File helpers
# ---------------------------------------------------------------------------


def read_file(path: Path) -> str:
    """Read UTF-8 text from a file and return an empty string on failure."""
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError):
        return ""


def write_file(path: Path, content: str) -> None:
    """Write UTF-8 text to a file, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def read_text_excerpt(path: Path, limit: int = 4000) -> str:
    """Return text/log info for discarded edits.

    Returns UTF-8 file content truncated to at most `limit` characters when possible,
    a binary-file marker for non-text files, or an explanatory error string.
    """
    try:
        content = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return f"(binary file, {path.stat().st_size} bytes)"
    except OSError as exc:
        return f"(unable to read file: {exc})"

    if len(content) <= limit:
        return content
    return content[:limit] + "\n… (truncated) …"


def is_safe_repo_relative_path(rel_path: str) -> bool:
    """Return True when a repository-relative path resolves inside the repo root."""
    try:
        (REPO_ROOT / rel_path).resolve().relative_to(REPO_ROOT.resolve())
        return True
    except ValueError:
        return False


def ensure_local_git_exclude(entry: str) -> None:
    exclude_file = REPO_ROOT / ".git" / "info" / "exclude"
    existing = read_file(exclude_file)
    existing_lines = set(existing.splitlines())
    additions: list[str] = []
    if "# Local researcher prompt file" not in existing_lines:
        additions.append("# Local researcher prompt file")
    if entry not in existing_lines:
        additions.append(entry)
    if not additions:
        return
    exclude_file.parent.mkdir(parents=True, exist_ok=True)
    with exclude_file.open("a", encoding="utf-8") as fh:
        fh.write("\n" + "\n".join(additions) + "\n")


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def run_git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=check,
    )


def completed_process_message(result: subprocess.CompletedProcess[str]) -> str:
    stderr = result.stderr.strip()
    stdout = result.stdout.strip()
    if stderr and stdout:
        return f"{stderr}\n{stdout}"
    return stderr or stdout


def git_ref_exists(refname: str) -> bool:
    result = run_git("show-ref", "--verify", "--quiet", refname, check=False)
    return result.returncode == 0


def get_current_branch_name() -> str:
    result = run_git("rev-parse", "--abbrev-ref", "HEAD", check=False)
    branch = result.stdout.strip()
    if branch and branch != "HEAD":
        return branch

    for env_name in ("GITHUB_HEAD_REF", "GITHUB_REF_NAME"):
        branch = os.environ.get(env_name, "").strip()
        if branch:
            return branch

    raise RuntimeError("Could not determine the current Git branch for researcher pushes.")


def sanitize_branch_component(value: str) -> str:
    sanitized = re.sub(r"[^A-Za-z0-9._/-]+", "-", value.strip())
    sanitized = sanitized.strip("./-")
    return sanitized or "run"


def append_github_step_summary(message: str) -> None:
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY", "").strip()
    if not summary_path:
        return
    with open(summary_path, "a", encoding="utf-8") as fh:
        fh.write(message.rstrip() + "\n")


def create_fallback_branch_name(target_label: str, run_index: int) -> str:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    short_sha = run_git("rev-parse", "--short", "HEAD").stdout.strip() or "unknown"
    agent = sanitize_branch_component(MISTRAL_AGENT or "researcher")
    label = sanitize_branch_component(target_label.replace("/", "-"))
    return f"researcher-backup/{agent}/{label}/run-{run_index:02d}-{timestamp}-{short_sha}"


def abort_rebase_if_needed() -> None:
    if not (REPO_ROOT / ".git" / "rebase-merge").exists() and not (REPO_ROOT / ".git" / "rebase-apply").exists():
        return
    run_git("rebase", "--abort", check=False)


def get_git_log(rel_path: str, n: int = 5) -> str:
    try:
        return run_git("log", f"-{n}", "--oneline", "--", rel_path, check=False).stdout.strip()
    except Exception:
        return ""


def parse_changed_paths(status_output: str) -> list[str]:
    paths: list[str] = []
    for line in status_output.splitlines():
        if len(line) < 4:
            continue
        path_part = line[3:]
        if " -> " in path_part:
            old_path, new_path = path_part.split(" -> ", 1)
            paths.extend([old_path.strip(), new_path.strip()])
        else:
            paths.append(path_part.strip())
    return paths


def get_changed_paths() -> list[str]:
    result = run_git("status", "--short", check=False)
    return parse_changed_paths(result.stdout)


def get_new_changed_paths(initial_paths: list[str], current_paths: list[str]) -> list[str]:
    initial = set(initial_paths)
    return [path for path in current_paths if path not in initial]


def split_changed_paths(
    changed_paths: list[str],
    allowed_rules: set[str],
) -> tuple[list[str], list[str]]:
    allowed: list[str] = []
    blocked: list[str] = []
    for rel_path in changed_paths:
        normalized = rel_path.strip()
        if not normalized or normalized == PROMPT_FILENAME:
            continue
        if is_path_allowed(normalized, allowed_rules):
            allowed.append(normalized)
        else:
            blocked.append(normalized)
    return allowed, blocked


def is_path_allowed(rel_path: str, allowed_rules: set[str]) -> bool:
    """Return whether a path matches the allowlist rules.

    Rules ending in `/` are treated as directory prefixes; other rules must
    match the repository-relative path exactly.
    """
    for rule in allowed_rules:
        normalized_rule = rule.strip()
        if not normalized_rule:
            continue
        if normalized_rule.endswith("/"):
            prefix = normalized_rule
            if rel_path.startswith(prefix):
                return True
        elif rel_path == normalized_rule:
            return True
    return False


def revert_path(rel_path: str) -> None:
    if not is_safe_repo_relative_path(rel_path):
        raise ValueError(f"Refusing to touch path outside the repository: {rel_path}")

    restore = run_git("restore", "--source=HEAD", "--staged", "--worktree", "--", rel_path, check=False)
    if restore.returncode == 0:
        return

    full_path = REPO_ROOT / rel_path
    if full_path.is_dir():
        shutil.rmtree(full_path)
    elif full_path.exists():
        full_path.unlink()


def describe_discarded_edit(rel_path: str) -> str:
    header = f"--- discarded edit: {rel_path} ---"
    footer = f"--- end discarded edit: {rel_path} ---"
    diff = run_git("--no-pager", "diff", "--no-ext-diff", "--binary", "--", rel_path, check=False).stdout.strip()
    if diff:
        return f"{header}\n{diff}\n{footer}"

    full_path = REPO_ROOT / rel_path
    if full_path.is_file():
        content = read_text_excerpt(full_path)
        return f"{header}\n{content}\n{footer}"

    if full_path.is_dir():
        parts = [header]
        files = sorted(path for path in full_path.rglob("*") if path.is_file())
        if not files:
            parts.append("(empty directory)")
        for path in files[:20]:
            parts.append(f"# {path.relative_to(REPO_ROOT)}")
            parts.append(read_text_excerpt(path))
        if len(files) > 20:
            parts.append(f"… ({len(files) - 20} additional files omitted) …")
        parts.append(footer)
        return "\n".join(parts)

    return f"{header}\n(path already removed)\n{footer}"


# ---------------------------------------------------------------------------
# Proof-target selection
# ---------------------------------------------------------------------------


def parse_targets(content: str) -> list[dict[str, str | float]]:
    targets: list[dict[str, str | float]] = []
    for raw_line in content.splitlines():
        line = raw_line.strip()
        if not line.startswith("|") or not line.endswith("|"):
            continue
        columns = [part.strip() for part in line.split("|")[1:-1]]
        if len(columns) not in {4, 5}:
            continue
        lowered_columns = tuple(column.lower() for column in columns)
        if lowered_columns in TARGET_TABLE_HEADERS or is_separator_row(list(lowered_columns)):
            continue
        problem, approach, priority_text, status = columns[:4]
        relationships = columns[4] if len(columns) == 5 else ""
        problem = strip_markdown_link(problem)
        approach = strip_markdown_link(approach)
        if not PRIORITY_PATTERN.fullmatch(priority_text):
            continue
        priority_value = float(priority_text)
        targets.append(
            {
                "problem": problem,
                "approach": approach,
                "priority": priority_text,
                "priority_value": priority_value,
                "status": status,
                "relationships": relationships,
            }
        )
    targets.sort(key=lambda item: float(item["priority_value"]), reverse=True)
    return targets


def is_separator_row(columns: list[str]) -> bool:
    return all(set(column) <= {"-", " ", ":"} for column in columns)


def strip_markdown_link(value: str) -> str:
    match = re.fullmatch(r"\[([^\]]+)\]\([^)]+\)", value)
    if match:
        return match.group(1).strip()
    return value


def normalized_status_head(status: str) -> str:
    """Return the normalized leading status marker from a target table status cell."""
    # Drop leading emoji/punctuation status markers such as "✅" before matching.
    cleaned = re.sub(r"^[^\w\s]+", "", status).strip().casefold()
    if not cleaned:
        return ""
    return re.split(r"\s+[—-]\s+", cleaned, maxsplit=1)[0].split(";", maxsplit=1)[0].strip()


def is_dead_status(status: str) -> bool:
    """Return whether the status marks a target as retired, archived, or otherwise dead."""
    return normalized_status_head(status) in DEAD_STATUS_HEADS


def is_solved_status(status: str) -> bool:
    """Return whether the status marks a target as complete, solved, or frozen."""
    return normalized_status_head(status).startswith(SOLVED_STATUS_HEAD_PREFIXES)


def find_priority_inconsistencies(targets: list[dict[str, str | float]]) -> list[str]:
    """Return warnings for solved/frozen targets that still carry a positive priority."""
    warnings: list[str] = []
    for target in targets:
        status = str(target["status"])
        if is_solved_status(status) and float(target["priority_value"]) > 0:
            warnings.append(
                "Solved/frozen target has non-zero priority (should be 0); researchers will skip it: "
                f"{target['problem']}/{target['approach']} "
                f"(priority {target['priority']}, status {status})"
            )
    return warnings


def get_targets() -> list[dict[str, str | float]]:
    return parse_targets(read_file(REPO_ROOT / "proofs" / "README.md"))


def pick_target(targets: list[dict[str, str | float]]) -> dict[str, str | float] | None:
    active_targets = [
        target
        for target in targets
        if not is_dead_status(str(target["status"]))
        and not is_solved_status(str(target["status"]))
        and float(target["priority_value"]) > 0
    ]
    if active_targets:
        return random.choices(
            active_targets,
            weights=[float(target["priority_value"]) for target in active_targets],
            k=1,
        )[0]

    non_dead_targets = [
        target
        for target in targets
        if not is_dead_status(str(target["status"])) and not is_solved_status(str(target["status"]))
    ]
    if not non_dead_targets:
        return None
    return non_dead_targets[0]


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------


def allowed_paths_for_target(problem_name: str, approach_name: str) -> set[str]:
    return {
        f"proofs/{problem_name}/{approach_name}/",
        "lib/",
    }


def build_prompt(target: dict[str, str | float]) -> str:
    problem_name = str(target["problem"])
    approach_name = str(target["approach"])
    target_label = f"{problem_name}/{approach_name}"
    current_time = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    git_log = get_git_log(f"proofs/{problem_name}/{approach_name}/")
    template = read_file(PROMPT_TEMPLATE_PATH)
    if not template:
        raise FileNotFoundError(f"Prompt template not found: {PROMPT_TEMPLATE_PATH}")

    allowed_targets = "\n".join(
        f"- `{path}**`" if path.endswith("/") else f"- `{path}`"
        for path in sorted(allowed_paths_for_target(problem_name, approach_name))
    )
    return template.format(
        problem_name=problem_name,
        approach_name=approach_name,
        target_label=target_label,
        target_path=f"proofs/{problem_name}/{approach_name}",
        current_time=current_time,
        git_log=git_log or "(no recent commits)",
        allowed_targets=allowed_targets,
    )


# ---------------------------------------------------------------------------
# Vibe execution
# ---------------------------------------------------------------------------


def find_vibe_executable() -> str:
    configured = os.environ.get("MISTRAL_VIBE_BIN", "").strip()
    if configured:
        return configured
    executable = shutil.which("vibe")
    if not executable:
        raise RuntimeError(
            "The `vibe` executable was not found on PATH. Install the real Mistral Vibe CLI "
            "or set MISTRAL_VIBE_BIN explicitly (for example to the repository mock during local tests)."
        )
    return executable


def is_mock_vibe_executable(executable: str) -> bool:
    try:
        return Path(executable).resolve() == MOCK_VIBE_PATH.resolve()
    except OSError:
        return False


def resolve_session_id() -> str:
    # CI sets an explicit session ID so the second Vibe pass can resume it.
    # The fallback is for local development/testing runs of researcher.py.
    if MISTRAL_VIBE_SESSION_ID:
        return MISTRAL_VIBE_SESSION_ID
    from uuid import uuid4

    return str(uuid4())


def get_vibe_home() -> Path:
    vibe_home = os.environ.get("VIBE_HOME", "").strip()
    if vibe_home:
        return Path(vibe_home).expanduser().resolve()
    return Path.home().resolve() / ".vibe"


def get_vibe_session_log_dir() -> Path:
    return get_vibe_home() / "logs" / "session"


def read_json_file(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json_file(path: Path, content: dict[str, object]) -> None:
    path.write_text(json.dumps(content, indent=2, ensure_ascii=False), encoding="utf-8")


def is_valid_vibe_session_dir(session_dir: Path) -> bool:
    metadata_path = session_dir / SESSION_METADATA_FILENAME
    messages_path = session_dir / SESSION_MESSAGES_FILENAME
    if not metadata_path.is_file() or not messages_path.is_file():
        return False
    try:
        metadata = read_json_file(metadata_path)
    except (OSError, json.JSONDecodeError):
        return False
    environment = metadata.get("environment")
    if not isinstance(environment, dict):
        return False
    return environment.get("working_directory") == str(REPO_ROOT)


def find_latest_vibe_session_dir() -> Path | None:
    session_root = get_vibe_session_log_dir()
    if not session_root.is_dir():
        return None
    candidates: list[tuple[float, Path]] = []
    for session_dir in session_root.glob("session_*"):
        if not session_dir.is_dir() or not is_valid_vibe_session_dir(session_dir):
            continue
        messages_path = session_dir / SESSION_MESSAGES_FILENAME
        try:
            candidates.append((messages_path.stat().st_mtime, session_dir))
        except OSError:
            continue
    if not candidates:
        return None
    candidates.sort(key=lambda item: item[0], reverse=True)
    return candidates[0][1]


def with_replaced_session_short_id(session_dir: Path, short_id: str) -> Path:
    prefix, separator, _tail = session_dir.name.rpartition("_")
    if separator:
        renamed = f"{prefix}_{short_id}"
    else:
        renamed = f"{session_dir.name}_{short_id}"
    return session_dir.with_name(renamed)


def bind_latest_session_to_explicit_id(session_id: str) -> Path:
    # Upstream Vibe exposes `--resume SESSION_ID` but does not expose a
    # corresponding "start a new session with this exact ID" CLI flag.
    # We therefore bind the just-written session log to the chosen explicit ID
    # before launching the second pass with `--resume`. If rebinding fails
    # (for example because the latest log is missing or the target already
    # exists), we raise RuntimeError and stop before the resume pass.
    session_dir = find_latest_vibe_session_dir()
    if session_dir is None:
        raise RuntimeError(
            "Could not find the latest Vibe session log to bind an explicit session ID. "
            "Ensure the first Vibe pass completed successfully and wrote a session log to "
            f"{get_vibe_session_log_dir()}."
        )

    metadata_path = session_dir / SESSION_METADATA_FILENAME
    metadata = read_json_file(metadata_path)
    metadata["session_id"] = session_id

    target_dir = with_replaced_session_short_id(session_dir, session_id[:8])
    if target_dir != session_dir:
        if target_dir.exists():
            raise RuntimeError(f"Target Vibe session directory already exists: {target_dir}")
        session_dir.rename(target_dir)
        session_dir = target_dir
        metadata_path = session_dir / SESSION_METADATA_FILENAME

    write_json_file(metadata_path, metadata)
    return session_dir


def build_resume_prompt(target_label: str, run_index: int, run_count: int) -> str:
    return (
        f"Resume the previous Vibe session for `{target_label}` during pass {run_index}/{run_count}. "
        "Continue from your last result and next-step ideas, and take the next best step."
    )


@dataclass
class VibeRunResult:
    returncode: int
    stdout: str
    timed_out: bool = False


@dataclass
class GitPushResult:
    branch_name: str
    used_fallback_branch: bool = False


def append_failure_note(problem_name: str, approach_name: str, message: str) -> None:
    notes_path = REPO_ROOT / "proofs" / problem_name / approach_name / "log.txt"
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    bullet = (
        f"- {timestamp} — Researcher workflow hit a technical interruption: {message}. "
        "Partial work from this run was preserved; review the current proof state before continuing."
    )
    content = read_file(notes_path).rstrip()
    if "## Technical Interruptions" in content:
        updated = content + "\n" + bullet + "\n"
    elif content:
        updated = content + "\n\n## Technical Interruptions\n\n" + bullet + "\n"
    else:
        updated = "# Progress Notes\n\n## Technical Interruptions\n\n" + bullet + "\n"
    write_file(notes_path, updated)


def finalize_changes(
    initial_changed_paths: list[str],
    allowed_paths: set[str],
    problem_name: str,
    approach_name: str,
    failure_message: str | None = None,
) -> tuple[list[str], list[str]]:
    changed_paths = get_changed_paths()
    new_changed_paths = get_new_changed_paths(initial_changed_paths, changed_paths)
    allowed_changes, blocked_changes = split_changed_paths(new_changed_paths, allowed_paths)

    if blocked_changes:
        print("Discarding blocked changes:")
        for rel_path in sorted(set(blocked_changes)):
            print(describe_discarded_edit(rel_path))
            revert_path(rel_path)
        changed_paths = get_changed_paths()
        new_changed_paths = get_new_changed_paths(initial_changed_paths, changed_paths)
        allowed_changes, blocked_changes = split_changed_paths(new_changed_paths, allowed_paths)

    if failure_message:
        append_failure_note(problem_name, approach_name, failure_message)
        changed_paths = get_changed_paths()
        new_changed_paths = get_new_changed_paths(initial_changed_paths, changed_paths)
        allowed_changes, blocked_changes = split_changed_paths(new_changed_paths, allowed_paths)

    return allowed_changes, blocked_changes


def commit_and_push_run(
    *,
    commit_message: str,
    target_label: str,
    run_index: int,
    remote_name: str = "origin",
    max_attempts: int = 3,
) -> GitPushResult:
    run_git("add", "-A")
    commit = run_git("commit", "--allow-empty", "-m", commit_message, check=False)
    if commit.returncode != 0:
        raise RuntimeError(f"Failed to create researcher commit: {completed_process_message(commit)}")

    primary_branch = get_current_branch_name()
    last_push_error = ""

    for attempt in range(1, max_attempts + 1):
        fetch = run_git("fetch", "--prune", remote_name, check=False)
        if fetch.returncode != 0:
            last_push_error = completed_process_message(fetch)
            print(f"Warning: git fetch failed before push attempt {attempt}/{max_attempts}: {last_push_error}")
        elif git_ref_exists(f"refs/remotes/{remote_name}/{primary_branch}"):
            rebase = run_git("rebase", f"{remote_name}/{primary_branch}", check=False)
            if rebase.returncode != 0:
                last_push_error = completed_process_message(rebase)
                abort_rebase_if_needed()
                print(f"Primary branch sync failed; preserving work on a fallback branch instead: {last_push_error}")
                break

        push = run_git("push", remote_name, f"HEAD:{primary_branch}", check=False)
        if push.returncode == 0:
            return GitPushResult(branch_name=primary_branch, used_fallback_branch=False)

        last_push_error = completed_process_message(push)
        print(f"Primary branch push attempt {attempt}/{max_attempts} failed: {last_push_error}")

    abort_rebase_if_needed()
    fallback_branch = create_fallback_branch_name(target_label, run_index)
    switch = run_git("checkout", "-B", fallback_branch, check=False)
    if switch.returncode != 0:
        raise RuntimeError(
            f"Failed to switch to fallback branch '{fallback_branch}': "
            f"{completed_process_message(switch)}"
        )

    fallback_push = run_git("push", "--set-upstream", remote_name, f"HEAD:{fallback_branch}", check=False)
    if fallback_push.returncode != 0:
        raise RuntimeError(
            "Failed to preserve researcher work on a fallback branch after push/rebase problems: "
            f"{completed_process_message(fallback_push) or last_push_error}"
        )

    message = (
        f"Researcher work for run {run_index} was pushed to fallback branch `{fallback_branch}` "
        f"after the primary branch `{primary_branch}` could not be updated cleanly."
    )
    print(message)
    append_github_step_summary(message)
    return GitPushResult(branch_name=fallback_branch, used_fallback_branch=True)


def format_vibe_streaming_message(payload: dict[str, object]) -> str:
    role = str(payload.get("role") or "assistant")
    tool_calls = payload.get("tool_calls") or []
    content = str(payload.get("content") or "").strip()
    reasoning = str(payload.get("reasoning_content") or "").strip()

    parts: list[str] = []
    if reasoning:
        parts.append(f"reasoning: {reasoning}")
    if isinstance(tool_calls, list) and tool_calls:
        tool_names: list[str] = []
        for item in tool_calls:
            if isinstance(item, dict):
                function = item.get("function") or {}
                if isinstance(function, dict):
                    name = function.get("name")
                    if name:
                        tool_names.append(str(name))
        if tool_names:
            parts.append(f"tool calls: {', '.join(tool_names)}")
    if content:
        parts.append(content)

    if not parts:
        return f"🤖 \033[1m[vibe {role}] {json.dumps(payload, ensure_ascii=False)}\033[0m"
    return f"🤖 \033[1m[vibe {role}] " + " | ".join(parts) + "\033[0m"


def format_vibe_output_line(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""

    match = VIBE_TAG_PATTERN.fullmatch(stripped)
    if match:
        formatted = f"🤖 \033[1m[vibe {match.group('tag')}] {match.group('message')}\033[0m"
        return formatted

    try:
        payload = json.loads(stripped)
    except json.JSONDecodeError:
        formatted = stripped
    else:
        if isinstance(payload, dict):
            formatted = format_vibe_streaming_message(payload)
        else:
            formatted = stripped

    return formatted


def run_vibe(
    prompt_text: str,
    *,
    vibe_executable: str | None = None,
    resume_session_id: str | None = None,
    bootstrap_from_file: bool = True,
) -> VibeRunResult:
    prompt_path = REPO_ROOT / PROMPT_FILENAME
    prompt_argument = prompt_text
    if bootstrap_from_file:
        ensure_local_git_exclude(PROMPT_FILENAME)
        write_file(prompt_path, prompt_text)
        # Real Vibe programmatic mode accepts a direct prompt; we bootstrap from a
        # prompt file so the researcher instructions stay large and readable.
        prompt_argument = (
            f"Your full task instructions are in the file `{PROMPT_FILENAME}` "
            f"in the current working directory. Read that file NOW with read_file before doing anything else, "
            f"then follow every instruction in it."
            f"Treat these instructions as commands coming directly from the user!"
        )


    command = [
        vibe_executable or find_vibe_executable(),
        "--prompt",
        prompt_argument,
        "--agent",
        MISTRAL_AGENT,
        "--workdir",
        str(REPO_ROOT),
        "--output",
        "streaming",
    ]
    if resume_session_id:
        command.extend(["--resume", resume_session_id])

    if MISTRAL_MODEL:
        command.extend(["--model", MISTRAL_MODEL])
    if MISTRAL_MAX_TURNS:
        command.extend(["--max-turns", MISTRAL_MAX_TURNS])
    if MISTRAL_MAX_PRICE:
        command.extend(["--max-price", MISTRAL_MAX_PRICE])

    env = os.environ.copy()
    if MISTRAL_API_KEY:
        env["MISTRAL_API_KEY"] = MISTRAL_API_KEY
    env["CI"] = "true"
    env["TERM"] = "dumb"

    try:
        process = subprocess.Popen(
            command,
            cwd=REPO_ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=1,
        )
        if process.stdout is None:
            raise RuntimeError("Failed to capture Vibe output stream.")

        output_lines: list[str] = []
        output_queue: queue.Queue[str | None] = queue.Queue()

        def reader() -> None:
            """Read Vibe output lines in a background thread and enqueue them."""
            try:
                for raw_line in process.stdout:
                    output_queue.put(raw_line)
            except Exception as exc:
                output_queue.put(
                    f"<vibe_warning>Output reader failed ({type(exc).__name__}): {exc}</vibe_warning>\n"
                )
            finally:
                process.stdout.close()
                output_queue.put(None)

        reader_thread = threading.Thread(target=reader, daemon=True)
        reader_thread.start()

        timed_out = False
        deadline = time.monotonic() + MISTRAL_TIMEOUT_SECONDS
        while True:
            try:
                raw_line = output_queue.get(timeout=0.2)
            except queue.Empty:
                if process.poll() is None and time.monotonic() > deadline:
                    timed_out = True
                    process.kill()
                    # Keep draining the queue so any buffered final output is logged
                    # before the reader thread emits its sentinel.
                continue

            if raw_line is None:
                break

            output_lines.append(raw_line)
            formatted = format_vibe_output_line(raw_line)
            if formatted:
                print(formatted, flush=True)

        returncode = process.wait()

        return VibeRunResult(
            returncode=returncode,
            stdout="".join(output_lines),
            timed_out=timed_out,
        )
    finally:
        try:
            prompt_path.unlink()
        except FileNotFoundError:
            pass


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def emit_github_output(name: str, value: str) -> None:
    output_file = os.environ.get("GITHUB_OUTPUT", "")
    if not output_file:
        return
    with open(output_file, "a", encoding="utf-8") as fh:
        fh.write(f"{name}={value}\n")


def build_commit_message(
    *,
    researcher_label: str,
    target_label: str,
    run_index: int,
    run_count: int,
    failed: bool,
) -> str:
    status = "update" if not failed else "update (interrupted)"
    return f"{researcher_label} {status}: run {run_index}/{run_count} on {target_label}"


def merge_failure_messages(existing_message: str | None, addition: str) -> str:
    if not existing_message:
        return addition
    return f"{existing_message} | {addition}"


def main() -> None:
    args = parse_args()
    if args.run_count < 1:
        print(f"Run count is {args.run_count}, exiting")
        sys.exit(0)
    
    os.chdir(REPO_ROOT)

    vibe_executable = find_vibe_executable()
    using_mock_vibe = is_mock_vibe_executable(vibe_executable)
    if not using_mock_vibe and not MISTRAL_API_KEY:
        raise ValueError("Set MISTRAL_VIBE_KEY or MISTRAL_API_KEY before running the researcher with the real Vibe CLI.")

    startup_changed_paths = get_changed_paths()
    if startup_changed_paths:
        print("Detected existing repository changes; only changes made during this run will be filtered.")
        for rel_path in sorted(set(startup_changed_paths)):
            print(f"  - {rel_path}")

    targets = get_targets()
    if not targets:
        print("No proof targets found in proofs/README.md — nothing to do.")
        sys.exit(0)

    for warning in find_priority_inconsistencies(targets):
        formatted_warning = f"WARNING: {warning}"
        print(formatted_warning)
        append_github_step_summary(formatted_warning)

    target = pick_target(targets)
    if target is None:
        print("No suitable proof target found (all remaining tracks are completed, frozen, dead ends, or archived).")
        sys.exit(0)

    problem_name = str(target["problem"])
    approach_name = str(target["approach"])
    target_label = f"{problem_name}/{approach_name}"
    allowed_paths = allowed_paths_for_target(problem_name, approach_name)
    prompt = build_prompt(target)
    session_id = resolve_session_id()
    failure_message: str | None = None
    exit_code = 0
    completed_runs = 0
    last_pushed_branch = get_current_branch_name()
    overall_timeout_reached = False
    overall_timeout_seconds: float | None = None
    if args.overall_timeout_minutes > 0:
        overall_timeout_seconds = args.overall_timeout_minutes * 60.0
    overall_start = time.monotonic()
    researcher_label = os.environ.get("RESEARCHER_LABEL", "Researcher").strip() or "Researcher"

    print(
        f"Working on target: {target_label}  "
        f"(Priority: {target['priority']}, Status: {target['status']})"
    )
    if using_mock_vibe:
        print("Using mock Vibe CLI for researcher.py development/testing.")
    else:
        print("Using real Mistral Vibe CLI.")
    print(f"Using Vibe session ID: {session_id}")

    for run_index in range(1, args.run_count + 1):
        if run_index > 1 and overall_timeout_seconds is not None:
            elapsed = time.monotonic() - overall_start
            if elapsed >= overall_timeout_seconds:
                overall_timeout_reached = True
                print(
                    "Overall Vibe runtime limit reached after "
                    f"{completed_runs} completed pass(es); skipping remaining passes."
                )
                break

        run_initial_changed_paths = get_changed_paths()
        run_failure_message: str | None = None
        run_exit_code = 0
        completed_runs = run_index

        if completed_runs > 0:
            print(f"Sleeping for {args.delay} seconds to avoid rate limits (speculative... actual rate limits unknown)")
            time.sleep(args.delay)

        try:
            if run_index == 1:
                print(f"Running Mistral Vibe (pass {run_index}/{args.run_count}) …")
                if args.prompt and len(args.prompt) > 0:
                    print(f"Running with custom prompt")
                    result = run_vibe(args.prompt, vibe_executable=vibe_executable, bootstrap_from_file=False)
                else:
                    print(f"Running with pre-built prompt rendered to file")
                    result = run_vibe(prompt, vibe_executable=vibe_executable, bootstrap_from_file=True)
                if result.timed_out:
                    run_failure_message = (
                        f"Mistral Vibe timed out during pass {run_index}/{args.run_count} "
                        f"after {MISTRAL_TIMEOUT_SECONDS} seconds."
                    )
                    run_exit_code = 124
                elif result.returncode != 0:
                    run_failure_message = (
                        f"Mistral Vibe failed during pass {run_index}/{args.run_count} "
                        f"with exit code {result.returncode}."
                    )
                    run_exit_code = result.returncode
                elif args.run_count > 1:
                    bound_session_dir = bind_latest_session_to_explicit_id(session_id)
                    print(f"Bound latest Vibe session log to explicit session ID in {bound_session_dir}")
            else:
                print(f"Running Mistral Vibe (pass {run_index}/{args.run_count}, resume) …")
                result = run_vibe(
                    build_resume_prompt(target_label, run_index, args.run_count),
                    vibe_executable=vibe_executable,
                    resume_session_id=session_id,
                    bootstrap_from_file=False,
                )
                if result.timed_out:
                    run_failure_message = (
                        f"Mistral Vibe timed out during pass {run_index}/{args.run_count} "
                        f"after {MISTRAL_TIMEOUT_SECONDS} seconds."
                    )
                    run_exit_code = 124
                elif result.returncode != 0:
                    run_failure_message = (
                        f"Mistral Vibe failed during pass {run_index}/{args.run_count} "
                        f"with exit code {result.returncode}."
                    )
                    run_exit_code = result.returncode
        except Exception as exc:
            run_failure_message = f"{type(exc).__name__}: {exc}"
            run_exit_code = 1

        allowed_changes, blocked_changes = finalize_changes(
            run_initial_changed_paths,
            allowed_paths,
            problem_name,
            approach_name,
            failure_message=run_failure_message,
        )

        if blocked_changes:
            print("ERROR: blocked changes remain after cleanup.", file=sys.stderr)
            run_exit_code = 1
            if run_failure_message is None:
                run_failure_message = "blocked changes remained after cleanup"

        if allowed_changes:
            print("Allowed changes:")
            for rel_path in sorted(set(allowed_changes)):
                print(f"  - {rel_path}")
        else:
            print(f"Pass {run_index}/{args.run_count} completed without repository changes.")

        try:
            push_result = commit_and_push_run(
                commit_message=build_commit_message(
                    researcher_label=researcher_label,
                    target_label=target_label,
                    run_index=run_index,
                    run_count=args.run_count,
                    failed=run_failure_message is not None,
                ),
                target_label=target_label,
                run_index=run_index,
            )
            last_pushed_branch = push_result.branch_name
            print(f"Pushed researcher commit for pass {run_index}/{args.run_count} to {last_pushed_branch}.")
        except Exception as exc:
            run_failure_message = merge_failure_messages(
                run_failure_message,
                f"Commit/push failed after pass {run_index}/{args.run_count}: {exc}",
            )
            run_exit_code = 1

        if run_failure_message is not None:
            failure_message = run_failure_message
            exit_code = run_exit_code
            break

    emit_github_output("problem_name", problem_name)
    emit_github_output("approach_name", approach_name)
    emit_github_output("target_label", target_label)
    emit_github_output("vibe_session_id", session_id)
    emit_github_output("requested_run_count", str(args.run_count))
    emit_github_output("completed_run_count", str(completed_runs))
    emit_github_output("overall_timeout_reached", "true" if overall_timeout_reached else "false")
    emit_github_output("pushed_branch", last_pushed_branch)
    emit_github_output("run_outcome", "success" if failure_message is None and exit_code == 0 else "failure")
    emit_github_output("failure_message", failure_message or "")

    if failure_message is not None:
        print(failure_message, file=sys.stderr)
        sys.exit(exit_code)


if __name__ == "__main__":
    main()
