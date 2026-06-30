/-! # Unary `<` gadget design probe (top-down, Risk C2 / C7, 2026-06-29)

`#eval` validation of the **unary strict-less-than gadget** the CliqueRel
verifier needs but `EvalCnfCmd` never built. EvalCnf only ever compares unary
values for *equality* (`eqBit`); the FlatClique relation's first two checks
(`fgraph_wf G = ∀ e ∈ edges, e.1 < numV ∧ e.2 < numV`, and
`list_ofFlatType numV l = ∀ v ∈ l, v < numV`) need a **strict order** test on
two unary `1`-blocks. There is no `<`/`≤` `Op`; the only comparison op is
`eqBit`. So `<` must be a *gadget* built from the proven primitives.

This probe settles the realization at the register-arithmetic level (no real
machines): a **lockstep consume loop** decides `a < b` on unary blocks
`replicate a 1` / `replicate b 1`.

⚠ **2026-06-30 FINDING + design fix (top-down).** The first realization
transcribed into `CliqueRelTM.ltBit` was a guarded lockstep loop:

    forBnd idx sa                       -- WRONG
      ifBit sa (ifBit sb (tail sa ;; tail sb) skip) skip

`Cmd.ifBit t` branches on `s.get t = [1]` **exactly** (single `1`-cell), NOT on
nonemptiness — so on operands of magnitude `> 1` the body never fired and the
gadget returned the wrong verdict (`ltBit 2 5` gave `[0]` though `2 < 5`). The
`lockstep` model below correctly captures nonemptiness, but `ifBit` does not
provide it. **The fix is simpler, not more complex:** `tail []` is `[]`, so an
*unconditional* drain needs no guard at all —

    ltBit dst A B idx:
      copy  LT_B B
      forBnd idx A (tail LT_B LT_B)      -- |A| = a iterations; A is only the bound
      nonEmpty dst LT_B                  -- LT_B = replicate (b−a) 1 ⇒ a<b iff non-empty

After `a` iterations `LT_B = replicate (b − a) 1` (truncated subtraction), which is
non-empty iff `b > a` iff `a < b`. This is the realization PROVEN in
`CliqueRelTM.ltBit_run` (axiom-clean). The two `#eval` models below
(`lockstep`-based `ltBit`, and the `drain`-based `ltBitDrain`) both agree with `<`.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/CliqueLtProbe.lean`
(every `#eval` must print `true`). -/

abbrev Reg := List Nat

/-- One lockstep step: while both non-empty, drop one cell from each. -/
def lockstep : Reg × Reg → Reg × Reg
  | (a, b) =>
      match a, b with
      | _ :: a', _ :: b' => (a', b')
      | _, _             => (a, b)

/-- Run `n` lockstep steps. -/
def lockstepN : Nat → Reg × Reg → Reg × Reg
  | 0, p => p
  | n + 1, p => lockstepN n (lockstep p)

/-- The gadget verdict: run `|A|` steps, then `a < b ⇔ A empty ∧ B non-empty`. -/
def ltBit (a b : Nat) : Bool :=
  let A : Reg := List.replicate a 1
  let B : Reg := List.replicate b 1
  let (sa, sb) := lockstepN A.length (A, B)
  sa.isEmpty && !sb.isEmpty

/-- The PROVEN realization (`CliqueRelTM.ltBit` / `ltBit_run`): unconditional
drain of `B`'s copy, `|A|` times, then a non-emptiness read. `tail []` is `[]`,
so no guard is needed. -/
def ltBitDrain (a b : Nat) : Bool :=
  let B : List Nat := List.replicate b 1
  let drained := (List.range a).foldl (fun r _ => r.tail) B    -- tail B, a times
  !drained.isEmpty

/-- Reference: actual `<` on the underlying Nats. -/
def ltSpec (a b : Nat) : Bool := a < b

/-! ## The gadget agrees with `<` over a grid of small values -/

def grid : List (Nat × Nat) :=
  (List.range 7).flatMap (fun a => (List.range 7).map (fun b => (a, b)))

#eval grid.all (fun p => ltBit p.1 p.2 == ltSpec p.1 p.2)
#eval grid.all (fun p => ltBitDrain p.1 p.2 == ltSpec p.1 p.2)   -- the PROVEN gadget

-- spot checks (eyeball)
#eval ltBit 0 0   -- false
#eval ltBit 0 1   -- true
#eval ltBit 2 5   -- true
#eval ltBit 5 2   -- false
#eval ltBit 3 3   -- false
#eval ltBit 4 4   -- false

/-! ## `≤` variant (not currently needed, recorded for completeness):
`a ≤ b ⇔ A empty` after `|A|` lockstep steps. -/
def leBit (a b : Nat) : Bool :=
  let A : Reg := List.replicate a 1
  let B : Reg := List.replicate b 1
  let (sa, _) := lockstepN A.length (A, B)
  sa.isEmpty

#eval grid.all (fun p => leBit p.1 p.2 == decide (p.1 ≤ p.2))
