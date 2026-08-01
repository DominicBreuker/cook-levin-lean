import Complexity.Meta.AxiomGate
import Complexity.Lang.PolyTime

set_option autoImplicit false

/-! # `Op.cost` is a faithful proxy for Turing-machine time — as ONE theorem

## Why this file exists (top-down, 2026-08-02)

Every reduction and verifier in this development is a `Cmd`, and every
"polynomial time" claim is a bound on `Cmd.cost` — a number the *layer's*
semantics computes, not a number of `stepFlatTM` steps. So a reviewer of
`CookLevinHonest.CookLevinStr` has to be satisfied that `Op.cost` does not
**undercharge**: if some op cost `1` while its compiled form took exponentially
many machine steps, then a "polynomial-cost" reduction would be an
exponential-time reduction and the theorem would be worth nothing. (This project
has already found one real bug of exactly that kind — the original unit-cost
`Op.cost`, under which `concat`/`copy` grew the state multiplicatively and the
output could be exponential in the layer cost. See ROADMAP, Risk C2, reason 2.)

That reviewer obligation was listed in `README.md` as something to *trust*. It
need not be: it is proven, and has been since the compiler was finished — but it
was spread over `Compile.paddedCompute_run`, `Compile.padBudget_le` and
`Compile.physStepBudget_poly`, none of which says it in one sentence.
`Compile.cost_is_time_proxy` below says it in one sentence, and is gated.

## What is proven, exactly

> **There is one fixed polynomial `p` such that for every `Cmd` `c`, every
> register frame `k` and every bit-level input state `s`, the compiled machine
> reaches a halting state within `p (State.size s + c.cost s + k + c.loopDepth)`
> steps — with the tape holding `c.eval s` on every register the program is
> allowed to touch (`paddedComputeTM`, the reduction machine), or in the
> accept/reject state matching the program's answer bit (`paddedBitDeciderTM`,
> the verifier machine).**

⚠ **Both** machines are covered, deliberately: the proof path compiles two, one
per direction of the free line (`toFrameworkWitness'` and
`DecidesLang.toDecidesBy`), and a claim about only the first would be an
overclaim.

`p` is `timeProxyBound`, and it is exhibited, not merely asserted to exist —
a reader can look at it. The two arguments beyond the input size and the cost
are per-program constants (`k` is the witness's `regBound`, `loopDepth` is the
program's static loop nesting), which is why the bound is *uniform*: one
polynomial, all programs.

**Both halves are load-bearing.** The step bound alone would be vacuous — a
machine that halts immediately satisfies it — so the theorem also carries the
halting-state and output conditions. Conversely, the output condition alone is
what `Compile.paddedCompute_run` already gave; the point here is that it comes
*with* a polynomial time bound in the layer's own cost.

## What is NOT proven, and does not need to be

The **converse** direction — that `Op.cost` does not *overcharge*, i.e. that
`c.cost s` is bounded by a polynomial in the compiled machine's actual running
time. Nothing in this development needs it: overcharging can only make our own
witnesses' `cost_le` obligations harder to discharge, never make a proven
polynomial bound weaker. Do not add it, and do not read this file as claiming
it.

The faithfulness of `stepFlatTM` *itself* as a model of a Turing machine is
untouched and irreducible. `Op.cost` is now measured against `stepFlatTM`;
whether `stepFlatTM` is a Turing machine remains a reading of
`Complexity/Complexity/MachineSemantics.lean`.
-/

namespace Complexity.Lang

/-- **The uniform time bound.** `padBudget`'s quadratic (the runtime
register-padding prologue) plus the compiler's own cubic `physStepBudget`,
both instantiated at a linear reparametrisation of
`n = State.size s + c.cost s + k + c.loopDepth`. Degree 3; the constants are
slack, not tight — `toFrameworkWitness'` only ever needs `inOPoly`. -/
def timeProxyBound (n : Nat) : Nat :=
  (3 * n + 2) * (10 * n + 16) + 4 + Compile.physStepBudget (6 * n + 4) (6 * n + 4)

theorem timeProxyBound_poly : inOPoly timeProxyBound := by
  have hlin : inOPoly (fun n => 6 * n + 4) :=
    inOPoly_add (inOPoly_mul (inOPoly_const 6) inOPoly_id) (inOPoly_const 4)
  have hphys : inOPoly (fun n => Compile.physStepBudget (6 * n + 4) (6 * n + 4)) :=
    inOPoly_comp (f := fun n => 6 * n + 4) (g := fun m => Compile.physStepBudget m m)
      hlin Compile.physStepBudget_poly
  have hquad : inOPoly (fun n => (3 * n + 2) * (10 * n + 16)) :=
    inOPoly_mul (inOPoly_add (inOPoly_mul (inOPoly_const 3) inOPoly_id) (inOPoly_const 2))
      (inOPoly_add (inOPoly_mul (inOPoly_const 10) inOPoly_id) (inOPoly_const 16))
  exact inOPoly_add (inOPoly_add hquad (inOPoly_const 4)) hphys

theorem timeProxyBound_mono : monotonic timeProxyBound := by
  intro a b h
  have hphys : Compile.physStepBudget (6 * a + 4) (6 * a + 4)
      ≤ Compile.physStepBudget (6 * b + 4) (6 * b + 4) :=
    Compile.physStepBudget_mono (by omega) (by omega)
  unfold timeProxyBound
  have hquad : (3 * a + 2) * (10 * a + 16) ≤ (3 * b + 2) * (10 * b + 16) := by gcongr
  omega

/-- **The concrete bound.** The compiled machine reaches a halting state within
`timeProxyBound (State.size s + c.cost s + k + c.loopDepth)` steps, and the tape
it halts on holds the layer's output on every register `c` is allowed to touch.

The hypotheses are the compiler's standing format/frame conditions, and every
live witness already supplies them: `enc_bit` gives `BitState`, `width_le` gives
`s.length ≤ regBound`, `usesBelow` gives `UsesBelow c regBound`. Nothing is
assumed about `c` beyond them. -/
theorem Compile.time_le_timeProxyBound (c : Cmd) (k : Nat) (s : State)
    (hbit : Compile.BitState s) (hwle : s.length ≤ k) (huses : Cmd.UsesBelow c k) :
    ∃ (t : Nat) (cfg : FlatTMConfig) (out : State) (res : List Nat),
      runFlatTM t (Compile.paddedComputeTM c k)
          (initFlatConfig (Compile.paddedComputeTM c k) [Compile.encodeTape s]) = some cfg
      ∧ haltingStateReached (Compile.paddedComputeTM c k) cfg = true
      ∧ cfg.tapes = [([], 0, Compile.encodeTape out ++ res)]
      ∧ Compile.ValidResidue res
      ∧ (∀ r, r < k → State.get out r = State.get (c.eval s) r)
      ∧ t ≤ timeProxyBound (State.size s + c.cost s + k + c.loopDepth) := by
  obtain ⟨res, hres, hrun, hhalt⟩ := Compile.paddedCompute_run c s k hbit hwle huses
  set K : Nat := k + 2 * c.loopDepth + 2 with hK
  set n : Nat := State.size s + c.cost s + k + c.loopDepth with hn
  refine ⟨_, _, c.eval (s ++ List.replicate K []), res, hrun, hhalt, rfl, hres, ?_, ?_⟩
  · -- the padded run's output agrees with `c.eval s` on every register `< k`
    exact Cmd.eval_agree c k huses
      (fun r _ => Compile.get_append_replicate_nil s K r)
  · -- the budget
    have hsize : State.size s ≤ n := by omega
    have hcost : c.cost s ≤ n := by omega
    have hlen : s.length ≤ n := by omega
    have hKle : K ≤ 3 * n + 2 := by rw [hK]; omega
    -- the padding prologue: quadratic
    have hpad : Compile.padBudget K s ≤ (3 * n + 2) * (10 * n + 16) := by
      refine le_trans (Compile.padBudget_le K s) ?_
      exact Nat.mul_le_mul hKle (by omega)
    -- the compiled body: `physStepBudget` at a linear reparametrisation
    have hG : State.size s + (s.length + K) + c.cost s + 2 ≤ 6 * n + 4 := by omega
    have hbody : Compile.physStepBudget
          (State.size s + (s.length + K) + c.cost s + 2) (c.cost s)
        ≤ Compile.physStepBudget (6 * n + 4) (6 * n + 4) :=
      Compile.physStepBudget_mono hG (by omega)
    unfold timeProxyBound
    omega

/-- **The same bound for the DECIDER machine.** The proof path compiles two
machines, not one: `paddedComputeTM` for reductions (`toFrameworkWitness'`) and
`paddedBitDeciderTM` for verifiers (`DecidesLang.toDecidesBy`). A time-proxy
claim covering only the first would be an overclaim, so here is the second.

Its extra hypothesis `h0` is what makes a decider a decider — register `0` holds
one answer bit — and every live `DecidesLang` supplies it from its `decides`
field. The conclusion is the non-vacuous one: the machine halts in the **accept**
or **reject** state according to that bit. -/
theorem Compile.deciderTime_le_timeProxyBound (c : Cmd) (k : Nat) (s : State) (b : Nat)
    (hbit : Compile.BitState s) (hwle : s.length ≤ k) (huses : Cmd.UsesBelow c k)
    (hb : b = 0 ∨ b = 1) (h0 : State.get (c.eval s) 0 = [b]) :
    ∃ (t : Nat) (cfg : FlatTMConfig),
      runFlatTM t (Compile.paddedBitDeciderTM c k)
          (initFlatConfig (Compile.paddedBitDeciderTM c k) [Compile.encodeTape s]) = some cfg
      ∧ haltingStateReached (Compile.paddedBitDeciderTM c k) cfg = true
      ∧ cfg.state_idx = (if b = 1 then 1 else 2) + (Compile k c).states
          + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states
      ∧ t ≤ timeProxyBound (State.size s + c.cost s + k + c.loopDepth) := by
  obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
    Compile.paddedBitDecider_run c s b k hbit hwle huses hb h0
  set K : Nat := k + 2 * c.loopDepth + 2 with hK
  set n : Nat := State.size s + c.cost s + k + c.loopDepth with hn
  refine ⟨_, cfg, hrun, hhalt, hstate, ?_⟩
  have hKle : K ≤ 3 * n + 2 := by rw [hK]; omega
  have hpad : Compile.padBudget K s ≤ (3 * n + 2) * (10 * n + 16) := by
    refine le_trans (Compile.padBudget_le K s) ?_
    exact Nat.mul_le_mul hKle (by omega)
  have hG : State.size s + (s.length + K) + c.cost s + 2 ≤ 6 * n + 4 := by omega
  have hbody : Compile.physStepBudget
        (State.size s + (s.length + K) + c.cost s + 2) (c.cost s)
      ≤ Compile.physStepBudget (6 * n + 4) (6 * n + 4) :=
    Compile.physStepBudget_mono hG (by omega)
  unfold timeProxyBound
  omega

/-- ★ **`Op.cost` is a faithful proxy for machine time.** ONE fixed polynomial
bounds the running time of **both** machines the proof path compiles — the
reduction machine and the decider machine — in the layer's own cost, uniformly
over every program and every input. And in both cases the machine really halts:
the first on the program's real output, the second in the accept/reject state
matching the program's answer bit.

This is the theorem that removes "trust that `Op.cost` is a faithful proxy for
time" from a reviewer's list. Read the module docstring for the one direction it
deliberately does not prove. -/
theorem Compile.cost_is_time_proxy :
    ∃ p : Nat → Nat, inOPoly p ∧ monotonic p ∧
      -- reductions: `PolyTimeComputableLang` → `polyTimeComputable'`
      (∀ (c : Cmd) (k : Nat) (s : State),
        Compile.BitState s → s.length ≤ k → Cmd.UsesBelow c k →
        ∃ (t : Nat) (cfg : FlatTMConfig) (out : State) (res : List Nat),
          runFlatTM t (Compile.paddedComputeTM c k)
              (initFlatConfig (Compile.paddedComputeTM c k) [Compile.encodeTape s]) = some cfg
          ∧ haltingStateReached (Compile.paddedComputeTM c k) cfg = true
          ∧ cfg.tapes = [([], 0, Compile.encodeTape out ++ res)]
          ∧ Compile.ValidResidue res
          ∧ (∀ r, r < k → State.get out r = State.get (c.eval s) r)
          ∧ t ≤ p (State.size s + c.cost s + k + c.loopDepth))
      -- verifiers: `DecidesLang` → `DecidesBy`/`inTimePoly`
      ∧ (∀ (c : Cmd) (k : Nat) (s : State) (b : Nat),
        Compile.BitState s → s.length ≤ k → Cmd.UsesBelow c k →
        (b = 0 ∨ b = 1) → State.get (c.eval s) 0 = [b] →
        ∃ (t : Nat) (cfg : FlatTMConfig),
          runFlatTM t (Compile.paddedBitDeciderTM c k)
              (initFlatConfig (Compile.paddedBitDeciderTM c k) [Compile.encodeTape s]) = some cfg
          ∧ haltingStateReached (Compile.paddedBitDeciderTM c k) cfg = true
          ∧ cfg.state_idx = (if b = 1 then 1 else 2) + (Compile k c).states
              + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states
          ∧ t ≤ p (State.size s + c.cost s + k + c.loopDepth)) :=
  ⟨timeProxyBound, timeProxyBound_poly, timeProxyBound_mono,
    fun c k s hbit hwle huses => Compile.time_le_timeProxyBound c k s hbit hwle huses,
    fun c k s b hbit hwle huses hb h0 =>
      Compile.deciderTime_le_timeProxyBound c k s b hbit hwle huses hb h0⟩

#assert_axioms_clean
  Complexity.Lang.timeProxyBound_poly
  Complexity.Lang.timeProxyBound_mono
  Complexity.Lang.Compile.time_le_timeProxyBound
  Complexity.Lang.Compile.deciderTime_le_timeProxyBound
  Complexity.Lang.Compile.cost_is_time_proxy

end Complexity.Lang
