#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
PROMPTS_DIR = REPO_ROOT / ".github" / "prompts"
PROMPT_FILENAME = ".mistral-researcher-prompt.md"
VIBE_TAG_PATTERN = re.compile(r"^<(?P<tag>[a-z_]+)>(?P<message>.*)</(?P=tag)>$")
MISTRAL_MODEL = os.environ.get("MISTRAL_MODEL", "").strip()
MISTRAL_TIMEOUT_SECONDS = int(os.environ.get("MISTRAL_TIMEOUT_SECONDS", "3600"))

AGENT_CONFIG = {
    "lean": {
        "display_name": "Lean",
        "vibe_agent": "lean",
        "api_key_env": "MISTRAL_LABS_KEY",
    },
    "devstral": {
        "display_name": "Devstral",
        "vibe_agent": "auto-approve",
        "api_key_env": "MISTRAL_VIBE_KEY",
    },
}


DEFAULT_PROMPT_TEMPLATE = """You are working in the GitHub repository `DominicBreuker/cook-levin-lean`.

Repository root: `{repo_root}`

Your task is to implement step {step_id} of the Cook-Levin repair plan from `README.md`.
The detailed step instructions come from `{prompt_path}` and are reproduced below.

Important instructions:
- You may modify repository files as needed, but do not modify, create, delete, or move anything under `.github/`.
- temporary files must be written to /tmp or, if you write then under the working directory, you must delete them before you finish 
- Read `README.md` before making changes so your work stays aligned with the global plan.
- Follow the step prompt closely and complete as much of the step as you can coherently finish in one run.
- If your changes materially advance the repository status, update the `Current status at a glance` section in `README.md` and mark the relevant step progress in the plan.
- Validate your work with `lake build` before finishing.
- Leave the repository in a consistent state. Run lake build first and if the build has errors, you must fix them first.
- Treat any files in the coqdoc folder as the blueprint for our desired outcome, they are documentation of a working proof written in Coq
- Your final response must be exactly one short line suitable for use as a git commit message. Do not include quotes, markdown, or any extra explanation.

Regarding your tooling:
- Lean tooling is expected to be available before you start: `lean`, `lake`, Mathlib cache, `rg`, and the `lean-lsp` MCP server.
- Prefer Lean MCP tools over blind guessing when working on `.lean` files:
  - `lean_diagnostic_messages` for fast per-file errors/warnings
  - `lean_goal` / `lean_term_goal` to inspect proof states
  - `lean_local_search`, `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` to find existing lemmas
  - `lean_multi_attempt` to compare tactic candidates
  - `lean_verify` before claiming a proof is complete or sound
- Use `import Mathlib` explicitly in proof files when you need Mathlib lemmas or tactics.
- Use `lake build` for whole-project checkpoints, but use Lean MCP diagnostics first for faster iteration.

Step instructions from `{prompt_path}`:

{step_prompt}
"""


@dataclass
class VibeRunResult:
    returncode: int
    stdout: str
    timed_out: bool


def positive_int(value: str) -> int:
    """Parse a strictly positive integer argument."""
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def non_negative_int(value: str) -> int:
    """Parse a non-negative integer argument."""
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be a non-negative integer")
    return parsed


def non_negative_float(value: str) -> float:
    """Parse a non-negative floating-point argument."""
    parsed = float(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be non-negative")
    return parsed


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments for the researcher runner."""
    parser = argparse.ArgumentParser(description="Run the Cook-Levin researcher agent.")
    parser.add_argument("--agent-model", type=str, required=True, help="Lean or Devstral")
    parser.add_argument("--run-count", type=positive_int, default=1, help="number of Vibe passes to execute")
    parser.add_argument(
        "--overall-timeout-minutes",
        type=non_negative_float,
        default=0.0,
        help="stop starting new passes once cumulative runtime reaches this many minutes; 0 disables the limit",
    )
    parser.add_argument("--step", type=str, default="", help="step number to run when no custom prompt is provided")
    parser.add_argument("--prompt", type=str, default="", help="custom prompt passed directly to Vibe")
    parser.add_argument("--delay", type=non_negative_int, default=60, help="delay in seconds between Vibe passes")
    return parser.parse_args(argv)


def normalize_agent_model(value: str) -> str:
    normalized = value.strip().lower()
    if normalized not in AGENT_CONFIG:
        raise ValueError(f"Unsupported agent model '{value}'. Expected one of: Lean, Devstral.")
    return normalized


def read_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_file(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def ensure_local_git_exclude(entry: str) -> None:
    exclude_file = REPO_ROOT / ".git" / "info" / "exclude"
    existing = exclude_file.read_text(encoding="utf-8") if exclude_file.exists() else ""
    lines = set(existing.splitlines())
    additions: list[str] = []
    if "# Local researcher prompt file" not in lines:
        additions.append("# Local researcher prompt file")
    if entry not in lines:
        additions.append(entry)
    if additions:
        exclude_file.parent.mkdir(parents=True, exist_ok=True)
        with exclude_file.open("a", encoding="utf-8") as handle:
            handle.write("\n" + "\n".join(additions) + "\n")


def resolve_step_prompt(step_value: str) -> tuple[int, Path, str]:
    if not step_value.strip():
        raise ValueError("Provide --step 1..13 when no custom prompt is supplied.")
    try:
        step_id = int(step_value)
    except ValueError as exc:
        raise ValueError(f"Invalid step number '{step_value}'. Expected an integer from 1 to 13.") from exc
    if step_id < 1 or step_id > 13:
        raise ValueError(f"Invalid step number '{step_value}'. Expected a value from 1 to 13.")
    prompt_path = PROMPTS_DIR / f"step{step_id:02d}.md"
    if not prompt_path.is_file():
        raise FileNotFoundError(f"Step prompt file not found: {prompt_path}")
    return step_id, prompt_path, read_file(prompt_path)


def build_prompt(custom_prompt: str, step_value: str) -> tuple[str, str, str]:
    custom_prompt = custom_prompt.strip()
    if custom_prompt:
        return custom_prompt, "custom prompt", ""
    step_id, prompt_path, prompt_content = resolve_step_prompt(step_value)
    relative_prompt_path = prompt_path.relative_to(REPO_ROOT).as_posix()
    prompt_text = DEFAULT_PROMPT_TEMPLATE.format(
        repo_root=REPO_ROOT,
        step_id=f"{step_id:02d}",
        prompt_path=relative_prompt_path,
        step_prompt=prompt_content.strip(),
    )
    return prompt_text, relative_prompt_path, f"{step_id:02d}"


def find_vibe_executable() -> str:
    configured = os.environ.get("MISTRAL_VIBE_BIN", "").strip()
    return configured or "vibe"


def choose_api_key(agent_model: str) -> tuple[str, str]:
    config = AGENT_CONFIG[agent_model]
    api_key = os.environ.get(config["api_key_env"], "").strip()
    if not api_key:
        raise ValueError(f"Set {config['api_key_env']} before running the researcher.")
    return config["vibe_agent"], api_key


def format_vibe_output_line(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""
    match = VIBE_TAG_PATTERN.fullmatch(stripped)
    if match:
        return f"[vibe {match.group('tag')}] {match.group('message')}"
    try:
        payload = json.loads(stripped)
    except json.JSONDecodeError:
        return stripped
    if isinstance(payload, dict):
        role = str(payload.get("role") or "assistant")
        content = str(payload.get("content") or "").strip()
        reasoning = str(payload.get("reasoning_content") or "").strip()
        parts = [part for part in (reasoning, content) if part]
        return f"[vibe {role}] {' | '.join(parts)}" if parts else f"[vibe {role}] {json.dumps(payload, ensure_ascii=False)}"
    return stripped


def run_vibe(prompt_text: str, *, vibe_executable: str, vibe_agent: str, api_key: str, bootstrap_from_file: bool) -> VibeRunResult:
    prompt_path = REPO_ROOT / PROMPT_FILENAME
    prompt_argument = prompt_text
    if bootstrap_from_file:
        ensure_local_git_exclude(PROMPT_FILENAME)
        write_file(prompt_path, prompt_text)
        prompt_argument = (
            f"Your full task instructions are in `{PROMPT_FILENAME}` in the current working directory. "
            f"Read that file now and follow it exactly."
        )

    command = [
        vibe_executable,
        "--prompt",
        prompt_argument,
        "--agent",
        vibe_agent,
        "--workdir",
        str(REPO_ROOT),
        "--output",
        "streaming",
    ]
    if MISTRAL_MODEL:
        command.extend(["--model", MISTRAL_MODEL])

    env = os.environ.copy()
    env["MISTRAL_API_KEY"] = api_key
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
            try:
                for raw_line in process.stdout:
                    output_queue.put(raw_line)
            finally:
                process.stdout.close()
                output_queue.put(None)

        threading.Thread(target=reader, daemon=True).start()
        timed_out = False
        deadline = time.monotonic() + MISTRAL_TIMEOUT_SECONDS

        while True:
            try:
                raw_line = output_queue.get(timeout=0.2)
            except queue.Empty:
                if process.poll() is None and time.monotonic() > deadline:
                    timed_out = True
                    process.kill()
                continue

            if raw_line is None:
                break

            output_lines.append(raw_line)
            formatted = format_vibe_output_line(raw_line)
            if formatted:
                print(formatted, flush=True)

        return VibeRunResult(returncode=process.wait(), stdout="".join(output_lines), timed_out=timed_out)
    finally:
        if prompt_path.exists():
            prompt_path.unlink()


def extract_commit_message(stdout: str) -> str:
    assistant_messages: list[str] = []
    plain_lines: list[str] = []

    for raw_line in stdout.splitlines():
        stripped = raw_line.strip()
        if not stripped or VIBE_TAG_PATTERN.fullmatch(stripped):
            continue
        try:
            payload = json.loads(stripped)
        except json.JSONDecodeError:
            plain_lines.append(stripped)
            continue
        if isinstance(payload, dict):
            role = str(payload.get("role") or "")
            content = str(payload.get("content") or "").strip()
            if role == "assistant" and content:
                assistant_messages.append(content)

    candidates: list[str] = []
    if assistant_messages:
        candidates.extend(reversed(assistant_messages[-1].splitlines()))
    candidates.extend(reversed(plain_lines))

    for candidate in candidates:
        cleaned = candidate.strip().strip("`*#>- ")
        cleaned = re.sub(r"(?i)^commit message:\s*", "", cleaned)
        cleaned = re.sub(r"\s+", " ", cleaned).strip()
        if cleaned:
            return cleaned
    return ""


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


def abort_rebase_if_needed() -> None:
    if (REPO_ROOT / ".git" / "rebase-merge").exists() or (REPO_ROOT / ".git" / "rebase-apply").exists():
        run_git("rebase", "--abort", check=False)


def current_branch() -> str:
    result = run_git("rev-parse", "--abbrev-ref", "HEAD", check=False)
    branch = result.stdout.strip()
    if branch and branch != "HEAD":
        return branch
    for env_name in ("GITHUB_HEAD_REF", "GITHUB_REF_NAME"):
        branch = os.environ.get(env_name, "").strip()
        if branch:
            return branch
    raise RuntimeError("Could not determine the current Git branch.")


def remote_branch_exists(remote_name: str, branch_name: str) -> bool:
    result = run_git("show-ref", "--verify", "--quiet", f"refs/remotes/{remote_name}/{branch_name}", check=False)
    return result.returncode == 0


def repository_has_changes() -> bool:
    result = run_git("status", "--porcelain", check=False)
    return bool(result.stdout.strip())


def commit_and_push(commit_message: str, *, remote_name: str = "origin") -> str:
    branch_name = current_branch()
    run_git("add", "-A")
    commit = run_git("commit", "-m", commit_message, check=False)
    if commit.returncode != 0:
        raise RuntimeError(f"Failed to create commit: {completed_process_message(commit)}")

    fetch = run_git("fetch", "--prune", remote_name, check=False)
    if fetch.returncode != 0:
        raise RuntimeError(f"Failed to fetch before push: {completed_process_message(fetch)}")

    if remote_branch_exists(remote_name, branch_name):
        rebase = run_git("rebase", f"{remote_name}/{branch_name}", check=False)
        if rebase.returncode != 0:
            abort_rebase_if_needed()
            raise RuntimeError(f"Failed to rebase before push: {completed_process_message(rebase)}")

    push = run_git("push", remote_name, f"HEAD:{branch_name}", check=False)
    if push.returncode != 0:
        raise RuntimeError(f"Failed to push commit: {completed_process_message(push)}")
    return branch_name


def emit_github_output(name: str, value: str) -> None:
    output_file = os.environ.get("GITHUB_OUTPUT", "").strip()
    if not output_file:
        return
    with open(output_file, "a", encoding="utf-8") as handle:
        handle.write(f"{name}={value}\n")


def fallback_commit_message(step_id: str) -> str:
    return f"Advance Cook-Levin plan step {step_id or 'custom'}"


def main() -> None:
    args = parse_args()
    os.chdir(REPO_ROOT)

    agent_model = normalize_agent_model(args.agent_model)
    vibe_agent, api_key = choose_api_key(agent_model)
    prompt_text, prompt_source, resolved_step_id = build_prompt(args.prompt, args.step)
    using_custom_prompt = bool(args.prompt.strip())
    vibe_executable = find_vibe_executable()

    completed_runs = 0
    overall_timeout_reached = False
    last_commit_message = ""
    last_pushed_branch = current_branch()
    overall_timeout_seconds = args.overall_timeout_minutes * 60.0 if args.overall_timeout_minutes > 0 else None
    overall_start = time.monotonic()
    failure_message = ""
    exit_code = 0

    print(f"Using {AGENT_CONFIG[agent_model]['display_name']} researcher agent.")
    print(f"Prompt source: {prompt_source}")

    for run_index in range(1, args.run_count + 1):
        if run_index > 1:
            if overall_timeout_seconds is not None and time.monotonic() - overall_start >= overall_timeout_seconds:
                overall_timeout_reached = True
                print("Overall runtime limit reached; skipping remaining passes.")
                break
            if args.delay > 0:
                print(f"Sleeping for {args.delay} seconds before pass {run_index}/{args.run_count}.")
                time.sleep(args.delay)

        print(f"Running Mistral Vibe (pass {run_index}/{args.run_count}) …")
        try:
            result = run_vibe(
                prompt_text,
                vibe_executable=vibe_executable,
                vibe_agent=vibe_agent,
                api_key=api_key,
                bootstrap_from_file=not using_custom_prompt,
            )
        except Exception as exc:
            failure_message = f"{type(exc).__name__}: {exc}"
            exit_code = 1
            break

        completed_runs = run_index
        commit_message = extract_commit_message(result.stdout) or fallback_commit_message(resolved_step_id)
        last_commit_message = commit_message

        if repository_has_changes():
            try:
                last_pushed_branch = commit_and_push(commit_message)
                print(f"Committed and pushed changes on {last_pushed_branch}: {commit_message}")
            except Exception as exc:
                failure_message = f"Commit/push failed after pass {run_index}/{args.run_count}: {exc}"
                exit_code = 1
                break
        else:
            print(f"Pass {run_index}/{args.run_count} produced no repository changes; skipping commit and push.")

        if result.timed_out:
            failure_message = (
                f"Mistral Vibe timed out during pass {run_index}/{args.run_count} after {MISTRAL_TIMEOUT_SECONDS} seconds."
            )
            exit_code = 124
            break
        if result.returncode != 0:
            failure_message = f"Mistral Vibe failed during pass {run_index}/{args.run_count} with exit code {result.returncode}."
            exit_code = result.returncode
            break

    emit_github_output("agent_model", AGENT_CONFIG[agent_model]["display_name"])
    emit_github_output("step_id", resolved_step_id)
    emit_github_output("prompt_source", prompt_source)
    emit_github_output("completed_run_count", str(completed_runs))
    emit_github_output("overall_timeout_reached", "true" if overall_timeout_reached else "false")
    emit_github_output("last_commit_message", last_commit_message)
    emit_github_output("pushed_branch", last_pushed_branch)
    emit_github_output("run_outcome", "success" if not failure_message and exit_code == 0 else "failure")
    emit_github_output("failure_message", failure_message)

    if failure_message:
        print(failure_message, file=sys.stderr)
        sys.exit(exit_code)


if __name__ == "__main__":
    main()
