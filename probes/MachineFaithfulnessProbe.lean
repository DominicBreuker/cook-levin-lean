import Mathlib.Computability.TuringMachine.PostTuringMachine
import Complexity.MachineFaithfulness

set_option autoImplicit false

/-! # Is `FlatTM` a Turing machine? — the go/no-go probe (~3 s)

Top-down session 2026-08-09. This file is the **evidence** behind ROADMAP risk
**S10** and behind the caveats in `CookLevin/Complexity/MachineFaithfulness.lean`.
It answers the three questions the handoff posed before any simulation is built,
and it does so against Mathlib's *actual* `Turing.TM0` definitions rather than
from memory.

Sections §1–§3 are **negative controls**: they show the locality theorems of
`MachineFaithfulness.lean` have content, by exhibiting the rejected model in
which they are false. §§4–6 are the go/no-go itself, and §7 checks that the
run-level bound is attained rather than slack.

Run it with:

```
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH=$(lake env printenv LEAN_PATH)
lean probes/MachineFaithfulnessProbe.lean
```

Everything must elaborate **silently**: `#guard` turns a false claim into an
error, so "no output" is the pass condition. Measured runtime **2.4 s**, almost
all of it the Mathlib import.
-/

namespace MachineFaithfulnessProbe

open Complexity.MachineFaithfulness

/-! ## §1 · Locality is not free — the model that was rejected

Before the 2026-07-17 semantics fix, `writeCurrentTapeSymbol` zero-padded a
write beyond the frontier. `jumpWrite` below is that definition, verbatim. It is
the *negative control* for `MachineFaithfulness.tapeCell_write_of_ne`: under it,
**one step changes cells arbitrarily far from the head**, so no three-cell-window
tableau can simulate the machine and `cookTableau_correct` was false as stated.

Read the two `#guard`s together: with the head at cell `4` on a tape holding one
written cell, a single `jumpWrite` materialises `0`s at cells `1`, `2` and `3` —
three cells the head is not on. -/

/-- The pre-2026-07-17 write, kept only as a counterexample. -/
def jumpWrite (tape : List Nat × Nat × List Nat) (symbol : Option Nat) :
    List Nat × Nat × List Nat :=
  let head := tape.2.1
  let right := tape.2.2
  match symbol with
  | none => tape
  | some sym =>
      if head < right.length then
        (tape.1, head, right.take head ++ sym :: right.drop (head + 1))
      else
        (tape.1, head, right ++ List.replicate (head - right.length) 0 ++ [sym])

/-! ⚠ **Non-local**: the head is at `4`, and cells `1`, `2`, `3` changed. -/
#guard jumpWrite ([], 4, [9]) (some 7) = (([], 4, [9, 0, 0, 0, 7]) :
  List Nat × Nat × List Nat)

/-! Cell `1` was blank before the step and is `some 0` after it, although the
head was on cell `4`. This is exactly what `tapeCell_write_of_ne` forbids. -/
#guard (jumpWrite ([], 4, [9]) (some 7)).2.2[1]? = some 0 &&
       (([], 4, [9]) : List Nat × Nat × List Nat).2.2[1]? == none

/-! The model in force does the opposite: strictly beyond the frontier the write
is **dropped**, and no cell changes at all. -/
#guard writeCurrentTapeSymbol ([], 4, [9]) (some 7) = (([], 4, [9]) :
  List Nat × Nat × List Nat)

/-! ## §2 · …and the price of locality, made concrete

The append-only rule is a genuine **restriction** relative to a textbook TM, and
this development does not hide it. The four lines below are the whole of it: two
tapes on which the head reads the *same* symbol (blank), given the *same* write,
end up different — one appends, the other drops.

So a `FlatTM` step's effect on the tape is **not** a function of `(state, symbol
read)` alone: it also consults the position of the frontier, which the machine
cannot see. `MachineFaithfulness.find?_congr_of_read` is therefore about the
*entry selected*, not about the tape effect, and the two must not be conflated.

★ **This is the obstruction that decides §5.** A TM0 simulation over the plain
alphabet `Option Nat` cannot reproduce it — a TM0 machine's action is a function
of what it reads — so the simulation needs one extra alphabet symbol marking the
frontier. -/

#guard currentTapeSymbol ([], 1, [5]) == (none : Option Nat)
#guard currentTapeSymbol ([], 2, [5]) == (none : Option Nat)

/-! At the frontier the write **appends**… -/
#guard writeCurrentTapeSymbol ([], 1, [5]) (some 7) = (([], 1, [5, 7]) :
  List Nat × Nat × List Nat)

/-! …one cell further right, reading the very same blank, it is **dropped**. -/
#guard writeCurrentTapeSymbol ([], 2, [5]) (some 7) = (([], 2, [5]) :
  List Nat × Nat × List Nat)

/-! ## §3 · The written region stays a prefix

`MachineFaithfulness.written_prefix` says the non-blank cells are always an
initial segment. §2 is why: a gap can never be created. The `#guard`s below walk
a small tape through the three write cases and read every cell back. -/

/-- Cell-by-cell readback of a tape, as the machine sees it. -/
def cells (t : List Nat × Nat × List Nat) (n : Nat) : List (Option Nat) :=
  (List.range n).map (tapeCell t)

#guard cells ([], 0, [3, 4]) 4 = [some 3, some 4, none, none]
/-! A frontier write extends the prefix by exactly one. -/
#guard cells (writeCurrentTapeSymbol ([], 2, [3, 4]) (some 5)) 4 =
  [some 3, some 4, some 5, none]
/-! A beyond-frontier write leaves the prefix alone — no gap appears. -/
#guard cells (writeCurrentTapeSymbol ([], 3, [3, 4]) (some 5)) 4 =
  [some 3, some 4, none, none]

/-! ## §4 · Question 1 — tape shape: is there a mapping into `Turing.Tape`?

**Verdict: yes for the *state*, no for the *step*, and the difference is §2.**

Ours is `(left, head : Nat, right)` with `left` provably inert
(`MachineFaithfulness.tapeStep_left`) and the head an index into `right`;
Mathlib's `Turing.Tape Γ` is two-way infinite and is read by
`Turing.Tape.nth : Tape Γ → ℤ → Γ`.

* **Configurations map, injectively.** Take `Γ := Option Nat` with `default =
  none`. Our observable tape is `tapeCell = right[·]?`, which is `none` exactly
  beyond `right.length`; since `right : List Nat` contains no blanks, distinct
  `right`s give distinct cell functions, and `ListBlank`'s quotient (which
  identifies a list with itself plus trailing blanks) collapses nothing. So the
  frontier **is** recoverable from the abstract tape: it is the first blank.
* **Steps do not map.** §2: at a blank cell the FlatTM write is sometimes
  performed and sometimes dropped, and `Turing.TM0.step` has no way to tell the
  two apart, because a TM0 action is a function of the symbol read. So
  **append-only does not survive the mapping**; a simulation needs the frontier
  marked *in the alphabet*, e.g. `Γ := Option (Option Nat)` with the extra layer
  marking "this is the frontier cell".

The type-level facts this rests on: -/

/-- Mathlib's tape is indexed by `ℤ`, ours by `Nat` — the left wall is ours
alone, and a simulation must mark cell `0` (or shift the input right by one). -/
example : Turing.Tape (Option Nat) → ℤ → Option Nat := Turing.Tape.nth

/-- Ours is indexed by `Nat`; there is no cell `-1` to move onto, which is the
content of `MachineFaithfulness.left_end_is_a_wall`. -/
example : (List Nat × Nat × List Nat) → Nat → Option Nat := tapeCell

/-! ## §5 · Question 3 — direction, and what a TM0 simulation would cost

**The direction a reviewer needs is "theirs simulates ours"** — it is the one
that says our model smuggles in no extra power. Below, the four obstructions,
each pinned against Mathlib's real definitions, with the cost of clearing it.

1. **One action per step.** `Turing.TM0.Stmt` is `move d | write a`: a TM0 step
   either writes *or* moves. `tapeStep` does both. Cost: 2 TM0 steps and one
   intermediate label per FlatTM step — a constant factor, so polynomial bounds
   transfer.
2. **No "stay".** `TMMove` has `Nmove`; `TM0.Stmt` has no counterpart. Cost:
   zero — write back the symbol just read, which the machine knows.
3. **Left wall.** `Tape.nth` is `ℤ`-indexed; ours is `Nat`-indexed and `Lmove`
   at `0` is a no-op. Cost: one marker symbol at cell `0`, or shift the input.
4. ★ **Append-only.** §2. Cost: one marker symbol at the frontier, plus the
   two-step "write, advance the marker" dance at a frontier write.

None is an obstruction *in principle*; all four are bookkeeping, and 1–4
together mean the alphabet is `Option Nat` decorated with two bits and the step
count is multiplied by a constant. The honest estimate is **2–4 sessions**, of
which most is `ListBlank`/`Tape.move` reasoning and a `Turing.Respects`
correspondence — comparable to Mathlib's own `TM1to0`.

⚠ **And that is why it is not the next thing to build.** What the simulation
would buy is a *second opinion* — "is this a Turing machine?" becomes "is
Mathlib's `Turing.TM0` one?" — not a new guarantee. The guarantee a reviewer
actually needs is that our step is **not stronger** than a TM step, and
`MachineFaithfulness.lean` §§2–7 give that directly, in eight theorems that
quantify over every machine, every tape and every cell. Obstruction 4 even shows
the simulation would be proving our model is *weaker*, which is the safe
direction and the one nobody was worried about. -/

/-- Obstruction 1, pinned: a TM0 statement is one action, and the two
constructors are all there are. -/
example : Turing.TM0.Stmt (Option Nat) → Bool
  | .move _ => true
  | .write _ => false

/-- Obstruction 2, pinned: `TMMove` has a third, "stay", constructor. -/
example : TMMove → Bool
  | .Lmove => true
  | .Rmove => true
  | .Nmove => false

/-- Obstruction 1 again, from the other side: a TM0 machine's action is a
function of the state and the **symbol read** only — which is exactly what §2
shows a FlatTM write is not. -/
example : Turing.TM0.Machine (Option Nat) Nat =
    (Nat → Option Nat → Option (Nat × Turing.TM0.Stmt (Option Nat))) := rfl

/-! ## §6 · Question 2 — symbols

**Verdict: no obstruction.** Ours are `Nat` bounded by `M.sig` with `Option` for
"off the written region"; Mathlib's are an arbitrary `Inhabited` type, so
`Γ := Option (Fin M.sig)` with `default := none` is available for any valid
machine, and `MachineFaithfulness.tapeStep_bounded` is exactly the closure
property needed to build the `Fin`-typed version.

⚠ One thing the probe *did* turn up, and it is worth a reader's attention.
`validFlatTM` bounds the symbols in the **transition table**, not the symbols on
the **initial tape** — and `ComputesBy.computes` runs `runFlatTM` directly, which
(unlike `execFlatTM`) does not check `isValidFlatTapes`. So an out-of-alphabet
symbol *can* reach the tape via a witness's `encode`.

It is harmless, and `MachineFaithfulness.stuck_of_symbol_ge_sig` is why: a valid
machine reading a symbol `≥ sig` has no entry that can match it, so it is stuck
and `runFlatTM` stalls. `sig` is enforced by the semantics, not merely declared.
The `#guard`s below exhibit the stall on a concrete machine. -/

/-- A valid one-tape machine over `sig = 2` with a single transition on `some 0`. -/
def sigM : FlatTM :=
  { sig := 2, tapes := 1, states := 2
    trans := [{ src_state := 0, src_tape_vals := [some 0], dst_state := 1,
                dst_write_vals := [some 1], move_dirs := [TMMove.Rmove] }]
    start := 0, halt := [false, true] }

#guard isValidFlatTM sigM

/-! On an in-alphabet tape it steps and halts. -/
#guard acceptsFlatTM sigM [[0]] 5

/-! ⚠ On a tape carrying the out-of-alphabet symbol `7` it is **stuck**: the run
returns the initial configuration and never reaches a halting state. -/
#guard (stepFlatTM sigM (initFlatConfig sigM [[7]])).isNone
#guard !(acceptsFlatTM sigM [[7]] 5)

/-! …and that is not an artifact of `execFlatTM`'s tape check: `runFlatTM`,
which is what `ComputesBy.computes` uses, stalls on it too. -/
#guard (runFlatTM 5 sigM (initFlatConfig sigM [[7]])).isSome &&
  !(runFlatTM 5 sigM (initFlatConfig sigM [[7]])).any
    (fun cfg => haltingStateReached sigM cfg)

/-! ## §7 · Space ≤ time, on a real run

`MachineFaithfulness.runFlatTM_init_local` proves that after `n` steps the tape
has grown by at most `n` cells and the head is within `n` of the left end. The
machine below writes one cell per step, so it **meets** the bound — the theorem
is not slack. -/

/-- Writes `1` and advances, forever: one new cell per step. -/
def growM : FlatTM :=
  { sig := 2, tapes := 1, states := 1
    trans := [{ src_state := 0, src_tape_vals := [none], dst_state := 0,
                dst_write_vals := [some 1], move_dirs := [TMMove.Rmove] }]
    start := 0, halt := [false] }

#guard isValidFlatTM growM

/-! After `n` steps: exactly `n` cells written and the head at `n`. The bound of
`runFlatTM_init_local` is attained. -/
#guard ((runFlatTM 6 growM (initFlatConfig growM [[]])).map
  (fun cfg => cfg.tapes.map (fun t => (t.2.1, t.2.2.length)))) = some [(6, 6)]

end MachineFaithfulnessProbe
