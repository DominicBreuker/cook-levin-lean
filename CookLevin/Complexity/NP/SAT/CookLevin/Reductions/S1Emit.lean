import Complexity.NP.SAT.CookLevin.Reductions.S1Cards
import Complexity.NP.SAT.CookLevin.Reductions.FrontPieces

set_option autoImplicit false
set_option maxRecDepth 8000

/-! # S1, part 5 — the emitter atom and the program stages **Σ**, **F**, **I**

Three of the five remaining stages of `S1Witness.s1Program`, plus the atom every
one of them (and stage C) is built from.

* **`emitBlk`** — append one bare unary block `FlatTCCFree.encNat v = 1^v 0` to
  an output register, reading `v` as the *length* of a source register. This is
  the only way large output is ever built: one unit-cost `appendOne` per cell
  inside a `forBnd`. **Never `concat` onto an output register** —
  `Op.cost (concat dst a b) = 2(|a|+|b|)+1` re-charges the whole destination per
  append, which alone would make the emitter quadratic in its own output
  (HANDOFF finding 2, 2026-07-25-c).
* **Σ** — `1^(PSg M)`, the target's `Sigma` register.
* **F** — `FlatTCCFree.encFinal (flattenFinal (guessFinal M))`, the target's
  `final` register.
* **I** — `FlatTCCFree.encNats (flattenString (preludeRow M s maxSize steps))`,
  the target's `init` register.

Methodology, as for stage C (`Reductions/S1Cards.lean`): **a pure `List.range`
model first, proven equal to the `Fin`-typed definition, then the machine proven
to compute the model.** `initBlocks`/`finBlocks` below are those models.

## Findings of this session (2026-07-26)

1. **Stage F needs no validity hypothesis** — and neither does its halt-bit
   lookup. `cookFinal` runs `q` over `[0, states]` and asks
   `M.halt.getD q false`; the emitter drains `PHALT` (the raw bit list) one head
   cell per `q`, and a drained-empty `head` yields `[]`, which the `ifBit` reads
   as *false* — exactly `getD`'s out-of-range value. So the `|halt| = states`
   conjunct of the guard is **not** needed by stage F, on any machine. (Stage C's
   halt-gated families get the same lookup for free, but they index `PHALT`
   *randomly*, so they still need the `forBnd`-bounded scan.)
2. **The head-cell value is maintained incrementally, never multiplied.**
   `hv sig q b = (sig+1)·(q+1) + b` is kept in one register that grows by
   `1^(sig+1)` per `q` iteration, and `b` is *the inner loop counter itself*
   (`forBnd` puts `1^i` in the counter register), so the innermost body is two
   `tallyReg`s and three constant appends — no multiplication anywhere inside a
   loop. **This is the template stage C repeats seven times.**
3. **Stage I's row is three consecutive runs, not one branching loop.** The
   prelude row's positional case split (`p < |s|` / `< |s|+maxSize` / else) is a
   *partition of the row into three consecutive segments*, so the emitter is
   three sequential loops bounded by the three registers that already hold those
   lengths (`SREG`, `3 = 1^maxSize`, `4 = 1^steps`) — no on-machine comparison of
   `p` against anything. The only genuinely positional datum is "is this the
   row's first cell", which is one flag register cleared by the first cell
   emitted (`EFST`).
4. **Stage I may assume the guard for `s[p] < sig`, and must.** `pKindAt`'s
   out-of-alphabet fallback (`s.getD p 0 ≥ M.sig` ⇒ blank) is unreachable under
   `list_ofFlatType M.sig s`, which the `Cmd.ifBit S1Parse.FLG` multiplex
   guarantees. Testing it on-machine would cost a `ltBit` per cell for a branch
   that never fires.

## The register frame (inside `S1Parse`'s pinned frame)

Registers `32`–`47` are the block `S1Parse` left free; `0`–`13` (stage P's
outputs) and `1`–`5` (the head layout / output registers) are untouched by
everything here. The five `EOUT_*` registers persist to stage M; `ESG`…`EK2`
are scratch that every stage reuses.

```
32 EOUT_S  Σ's output            37 ESG  1^(Sg M)      43 EJ1  loop counter
33 EOUT_I  I's output            38 EA   scratch       44 EJ2  loop counter
34 EOUT_C  C's output (later)    39 EB   scratch       45 EJ3  loop counter
35 EOUT_F  F's output            40 EC   scratch       46 EK1  scratch
36 EOUT_T  1^(steps+1) (later)   41 ED   scratch       47 EK2  scratch
                                 42 EE   scratch
```
-/

namespace S1Emit

open Complexity.Lang Complexity.Simulators HeadLayout

/-! ## The emitter register frame -/

/-- Σ's output: `1^(PSg M)`. -/
def EOUT_S : Var := 32
/-- I's output: `encNats (flattenString (preludeRow …))`. -/
def EOUT_I : Var := 33
/-- C's output: `encNats (S1Cards.cardBlocks M)` (stage C, not built here). -/
def EOUT_C : Var := 34
/-- F's output: `encFinal (flattenFinal (guessFinal M))`. -/
def EOUT_F : Var := 35
/-- M-yes's steps register: `1^(steps+1)` (not built here). -/
def EOUT_T : Var := 36
/-- `1^(Sg M)` — the Γ-band width, shared by Σ and I. -/
def ESG : Var := 37
def EA  : Var := 38
def EB  : Var := 39
def EC  : Var := 40
def ED  : Var := 41
def EE  : Var := 42
def EJ1 : Var := 43
def EJ2 : Var := 44
def EJ3 : Var := 45
def EK1 : Var := 46
def EK2 : Var := 47

/-! ## The atom: `emitBlk`

`FrontPieces.tallyReg cnt src dst` appends `1^|src|` cell by cell (one
`appendOne` per iteration of a `forBnd` bounded by `src`); one `appendZero`
terminates the block. Cost `≤ 3 + 5v + v²` for a block of value `v` — the `v²`
is `Cmd.run`'s loop-counter charge, not our doing. -/

/-- **The emitter atom.** Append `FlatTCCFree.encNat v = 1^v 0` to `dst`, with
`v` read as the length of `src`. `src` survives (it is only the loop bound);
`cnt` exits dirty. -/
def emitBlk (cnt src dst : Var) : Cmd :=
  FrontPieces.tallyReg cnt src dst ;; Cmd.op (.appendZero dst)

/-- **`emitBlk` is correct.** -/
theorem emitBlk_run (cnt src dst : Var) (s : State) (v : Nat)
    (hcd : cnt ≠ dst) (hsrc : State.get s src = List.replicate v 1) :
    State.get ((emitBlk cnt src dst).eval s) dst
        = State.get s dst ++ FlatTCCFree.encNat v
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((emitBlk cnt src dst).eval s) r = State.get s r) := by
  obtain ⟨hD, hF, -⟩ := FrontPieces.tallyReg_run cnt src dst s hcd
  have hev : (emitBlk cnt src dst).eval s
      = (Cmd.op (.appendZero dst)).eval ((FrontPieces.tallyReg cnt src dst).eval s) := by
    unfold emitBlk; rw [Cmd.eval_seq]
  refine ⟨?_, ?_⟩
  · rw [hev, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, hD, hsrc, List.length_replicate,
      FlatTCCFree.encNat, List.append_assoc]
  · intro r h1 h2
    rw [hev, Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ h1]
    exact hF r h1 h2

/-- **`emitBlk`'s cost**: `≤ 3 + 5v + v²` for a block of value `v`. The
quadratic term is `Cmd.run`'s per-iteration loop-counter charge. -/
theorem emitBlk_cost (cnt src dst : Var) (s : State) (hcd : cnt ≠ dst) :
    (emitBlk cnt src dst).cost s
      ≤ 3 + (State.get s src).length * 5
          + (State.get s src).length * (State.get s src).length := by
  have h := (FrontPieces.tallyReg_run cnt src dst s hcd).2.2
  have hz : (Cmd.op (.appendZero dst)).cost
      ((FrontPieces.tallyReg cnt src dst).eval s) = 1 := rfl
  have hev : (emitBlk cnt src dst).cost s
      = 1 + (FrontPieces.tallyReg cnt src dst).cost s
        + (Cmd.op (.appendZero dst)).cost ((FrontPieces.tallyReg cnt src dst).eval s) := by
    unfold emitBlk; rw [Cmd.cost_seq]
  rw [hev, hz]
  omega

/-- `emitBlk` stays inside a register bound. -/
theorem emitBlk_usesBelow (cnt src dst : Var) (k : Nat)
    (hc : cnt < k) (hs : src < k) (hd : dst < k) :
    Cmd.UsesBelow (emitBlk cnt src dst) k :=
  ⟨⟨hc, hs, hd⟩, hd⟩

/-! ## The Γ-band width `1^(Sg M)`

`Sg M = (sig+1)·(states+2) + 1` — the *only* multiplication in stages Σ / I, and
it is paid once, outside every loop (HANDOFF finding 2: hoist products). The
product itself is `BinaryCCFSATFree.unaryMulLoop_run` (`concat` in a `forBnd`);
`concat` is legitimate here because the register is `O(σQ)` cells, not `Θ(n⁵)`
of output. -/

private def sgPre : Cmd :=
  Cmd.op (.copy EA S1Parse.PSIG) ;; Cmd.op (.appendOne EA) ;;
  Cmd.op (.copy EB S1Parse.PSTATES) ;; Cmd.op (.appendOne EB) ;;
  Cmd.op (.appendOne EB) ;; Cmd.op (.clear ESG)

private def sgLoop : Cmd := Cmd.forBnd EJ1 EB (Cmd.op (.concat ESG ESG EA))

/-- `ESG := 1^(Sg M)`, off `PSIG`/`PSTATES`. -/
def loadSg : Cmd := sgPre ;; sgLoop ;; Cmd.op (.appendOne ESG)

private theorem sgPre_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1) :
    State.get (sgPre.eval s) EA = List.replicate (M.sig + 1) 1
    ∧ State.get (sgPre.eval s) EB = List.replicate (M.states + 2) 1
    ∧ State.get (sgPre.eval s) ESG = []
    ∧ (∀ r : Var, r ≠ EA → r ≠ EB → r ≠ ESG →
        State.get (sgPre.eval s) r = State.get s r) := by
  simp only [sgPre, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  refine ⟨?_, ?_, ?_, ?_⟩
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [hsig, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [hst, ← List.replicate_succ', ← List.replicate_succ']
  · rw [State.get_set_eq]
  · intro r h1 h2 h3
    repeat first
      | rw [State.get_set_ne _ _ _ _ h1]
      | rw [State.get_set_ne _ _ _ _ h2]
      | rw [State.get_set_ne _ _ _ _ h3]

/-- **The Γ-band width is on tape.** -/
theorem loadSg_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1) :
    State.get (loadSg.eval s) ESG = List.replicate (Sg M) 1
    ∧ (∀ r : Var, r ≠ EA → r ≠ EB → r ≠ ESG → r ≠ EJ1 →
        State.get (loadSg.eval s) r = State.get s r) := by
  obtain ⟨hA, hB, hZ, hFr⟩ := sgPre_run M s hsig hst
  set t := sgPre.eval s with ht
  clear_value t
  have hloop : sgLoop = Cmd.forBnd EJ1 EB (Cmd.op (.concat ESG ESG EA)) := rfl
  have hev : loadSg.eval s
      = (Cmd.op (.appendOne ESG)).eval (sgLoop.eval t) := by
    unfold loadSg; rw [Cmd.eval_seq, Cmd.eval_seq, ← ht]
  obtain ⟨hmul, hmulFr⟩ := BinaryCCFSATFree.unaryMulLoop_run EJ1 EB EA ESG
    t (M.sig + 1) (M.states + 2)
    (by decide) (by decide) (by decide) hA (by rw [hB]; simp) hZ
  have hSg : (M.states + 2) * (M.sig + 1) + 1 = Sg M := by
    show _ = (M.sig + 1) * (M.states + 2) + 1
    rw [Nat.mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hev, Cmd.eval_op]
    show State.get ((sgLoop.eval t).set ESG _) ESG = _
    rw [State.get_set_eq]
    show State.get (sgLoop.eval t) ESG ++ [1] = _
    rw [hloop, hmul, ← List.replicate_succ', hSg]
  · intro r h1 h2 h3 h4
    rw [hev, Cmd.eval_op]
    show State.get ((sgLoop.eval t).set ESG _) r = _
    rw [State.get_set_ne _ _ _ _ h3, hloop, hmulFr r h3 h4]
    exact hFr r h1 h2 h3

theorem loadSg_usesBelow : Cmd.UsesBelow loadSg 48 := by
  simp [loadSg, sgPre, sgLoop, Cmd.UsesBelow, Op.UsesBelow,
    EA, EB, ESG, EJ1, S1Parse.PSIG, S1Parse.PSTATES]

/-! ## Stage Σ

`PSg M = Sg M + (2·sig + 5)`: the Γ band, then the seven prelude symbol classes
(`pDelim`, `pBlank`, `pStar`, `pInitStar`, `pInitBlank`, then `sig` fixed
symbols and `sig` init-fixed symbols). -/

private def sigTail : Cmd :=
  Cmd.op (.appendOne EOUT_S) ;; Cmd.op (.appendOne EOUT_S) ;;
  Cmd.op (.appendOne EOUT_S) ;; Cmd.op (.appendOne EOUT_S) ;;
  Cmd.op (.appendOne EOUT_S)

private theorem sigTail_run (s : State) (n : Nat)
    (h : State.get s EOUT_S = List.replicate n 1) :
    State.get (sigTail.eval s) EOUT_S = List.replicate (n + 5) 1
    ∧ (∀ r : Var, r ≠ EOUT_S → State.get (sigTail.eval s) r = State.get s r) := by
  simp only [sigTail, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  refine ⟨?_, ?_⟩
  · simp only [State.get_set_eq]
    rw [h]
    rw [← List.replicate_succ', ← List.replicate_succ', ← List.replicate_succ',
      ← List.replicate_succ', ← List.replicate_succ']
  · intro r h1
    repeat rw [State.get_set_ne _ _ _ _ h1]

/-- **Stage Σ.** `EOUT_S := 1^(PSg M)` — the target's `Sigma` register. -/
def stageSig : Cmd :=
  loadSg ;; Cmd.op (.copy EOUT_S ESG) ;;
    FrontPieces.tallyReg EJ1 S1Parse.PSIG EOUT_S ;;
    FrontPieces.tallyReg EJ1 S1Parse.PSIG EOUT_S ;; sigTail

/-- **Stage Σ is correct.** The alphabet register holds the guess tableau's own
`Sigma`, and nothing outside the emitter's scratch is touched. -/
theorem stageSig_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1) :
    State.get (stageSig.eval s) EOUT_S = List.replicate (PSg M) 1
    ∧ (∀ r : Var, r ≠ EA → r ≠ EB → r ≠ ESG → r ≠ EJ1 → r ≠ EOUT_S →
        State.get (stageSig.eval s) r = State.get s r) := by
  obtain ⟨hSG, hFr0⟩ := loadSg_run M s hsig hst
  set s0 := loadSg.eval s with hs0
  clear_value s0
  set s1 := (Cmd.op (.copy EOUT_S ESG)).eval s0 with hs1
  have hs1_out : State.get s1 EOUT_S = List.replicate (Sg M) 1 := by
    rw [hs1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hSG
  have hs1_fr : ∀ r : Var, r ≠ EOUT_S → State.get s1 r = State.get s0 r := by
    intro r hr; rw [hs1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  have hs1_sig : State.get s1 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs1_fr S1Parse.PSIG (by decide),
      hFr0 S1Parse.PSIG (by decide) (by decide) (by decide) (by decide)]
    exact hsig
  clear_value s1
  obtain ⟨ht2, ht2fr, -⟩ := FrontPieces.tallyReg_run EJ1 S1Parse.PSIG EOUT_S s1 (by decide)
  set s2 := (FrontPieces.tallyReg EJ1 S1Parse.PSIG EOUT_S).eval s1 with hs2
  have hs2_out : State.get s2 EOUT_S = List.replicate (Sg M + M.sig) 1 := by
    rw [ht2, hs1_out, hs1_sig, List.length_replicate, ← List.replicate_add]
  have hs2_sig : State.get s2 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [ht2fr S1Parse.PSIG (by decide) (by decide)]; exact hs1_sig
  clear_value s2
  obtain ⟨ht3, ht3fr, -⟩ := FrontPieces.tallyReg_run EJ1 S1Parse.PSIG EOUT_S s2 (by decide)
  set s3 := (FrontPieces.tallyReg EJ1 S1Parse.PSIG EOUT_S).eval s2 with hs3
  have hs3_out : State.get s3 EOUT_S = List.replicate (Sg M + M.sig + M.sig) 1 := by
    rw [ht3, hs2_out, hs2_sig, List.length_replicate, ← List.replicate_add]
  clear_value s3
  obtain ⟨ht4, ht4fr⟩ := sigTail_run s3 _ hs3_out
  have hev : stageSig.eval s = sigTail.eval s3 := by
    unfold stageSig
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, ← hs0, ← hs1, ← hs2, ← hs3]
  have hPSg : Sg M + M.sig + M.sig + 5 = PSg M := by unfold PSg; omega
  refine ⟨by rw [hev, ht4, hPSg], ?_⟩
  intro r h1 h2 h3 h4 h5
  rw [hev, ht4fr r h5, ht3fr r h5 h4, ht2fr r h5 h4, hs1_fr r h5]
  exact hFr0 r h1 h2 h3 h4

theorem stageSig_usesBelow : Cmd.UsesBelow stageSig 48 := by
  simp [stageSig, loadSg, sgPre, sgLoop, sigTail, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow, EA, EB, ESG, EJ1, EOUT_S,
    S1Parse.PSIG, S1Parse.PSTATES]

/-! ## Stage F — the final patterns

`guessFinal M = (cookFinal M).map (List.map (emb M))` and `emb` is value
preserving, so the flat target is

    (range (states+1)).flatMap (fun q =>
      if halt q then (range (sig+1)).map (fun b => [hv sig q b]) else [])

— `Θ(states·σ)` singleton patterns. The emitter keeps `1^(hv sig q 0)` in one
register that grows by `1^(sig+1)` per `q`, and reads `b` off the **inner loop
counter itself**, so the innermost body is two `tallyReg`s and three constant
appends. No multiplication happens inside any loop. -/

/-- `encFinal` is a monoid homomorphism (the emitter appends pattern by
pattern). -/
theorem encFinal_append (as bs : List (List Nat)) :
    FlatTCCFree.encFinal (as ++ bs)
      = FlatTCCFree.encFinal as ++ FlatTCCFree.encFinal bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      show FlatTCCFree.encSList a ++ FlatTCCFree.encFinal (as ++ bs)
        = (FlatTCCFree.encSList a ++ FlatTCCFree.encFinal as) ++ _
      rw [ih, List.append_assoc]

/-- One singleton pattern's stream: the sentinel `1`, the block `1^v 0`, then
the list terminator `0`. -/
theorem encFinal_singleton (v : Nat) :
    FlatTCCFree.encFinal [[v]] = (1 :: (List.replicate v 1 ++ [0])) ++ [0] := by
  simp [FlatTCCFree.encFinal, FlatTCCFree.encSList, FlatTCCFree.encSElem]

/-- **Stage F's pure model.** Each halting state `q ≤ states` contributes the
`sig+1` singleton patterns `[hv sig q b]`; `hbits` is `S1Parse.PHALT`, the raw
halt bit list. -/
def finBlocks (sig states : Nat) (hbits : List Nat) : List (List Nat) :=
  (List.range (states + 1)).flatMap (fun q =>
    if S1Cards.haltBit hbits q then
      (List.range (sig + 1)).map (fun b => [S1Cards.hv sig q b])
    else [])

/-- **The model is the definition.** -/
theorem finBlocks_eq (M : FlatTM) :
    FlatTCC.flattenFinal (guessFinal M)
      = finBlocks M.sig M.states (M.halt.map S1Parse.bitOf) := by
  have hcomp : ((flattenString ∘ List.map (emb M)) : List (Fin (Sg M)) → List Nat)
      = flattenString := by
    funext l
    show (l.map (emb M)).map Fin.val = l.map Fin.val
    rw [List.map_map]; rfl
  show ((cookFinal M).map (List.map (emb M))).map flattenString = _
  rw [List.map_map, hcomp]
  unfold cookFinal finBlocks
  rw [List.map_flatMap]
  refine S1Cards.finRange_flatMap_congr (M.states + 1) _ _ (fun q => ?_)
  by_cases hq : M.halt.getD q.1 false = true
  · rw [if_pos hq, if_pos (show S1Cards.haltBit (M.halt.map S1Parse.bitOf) q.1 = true by
      rw [S1Cards.haltBit_eq]; exact hq), List.map_map]
    exact S1Cards.map_finRange_congr (M.sig + 1) _
      (fun b => [S1Cards.hv M.sig q.1 b]) (fun b => rfl)
  · rw [if_neg hq, if_neg (show ¬ (S1Cards.haltBit (M.halt.map S1Parse.bitOf) q.1 = true) by
      rw [S1Cards.haltBit_eq]; exact hq)]
    rfl

/-! ### The machine -/

/-- The emitter's no-op (register `0` must stay `[]` for the seam, so the
branch-free arm clears a scratch register instead). -/
def enop : Cmd := Cmd.op (.clear EK1)

/-- Stage F's preamble: `EA = 1^(sig+1)`, `EB = 1^(states+1)`,
`EC = 1^(hv sig 0 0)`, `ED` a draining copy of the halt bit list. -/
private def finPre : Cmd :=
  Cmd.op (.clear EOUT_F) ;;
  Cmd.op (.copy EA S1Parse.PSIG) ;; Cmd.op (.appendOne EA) ;;
  Cmd.op (.copy EB S1Parse.PSTATES) ;; Cmd.op (.appendOne EB) ;;
  Cmd.op (.copy EC EA) ;;
  Cmd.op (.copy ED S1Parse.PHALT)

/-- One `(q, b)` pattern: `encSList [hv sig q b]`, with `1^((sig+1)(q+1))` read
off `EC` and `1^b` off the loop counter `EJ2`. -/
private def finInner : Cmd :=
  Cmd.op (.appendOne EOUT_F) ;;
  FrontPieces.tallyReg EJ3 EC EOUT_F ;;
  FrontPieces.tallyReg EJ3 EJ2 EOUT_F ;;
  Cmd.op (.appendZero EOUT_F) ;;
  Cmd.op (.appendZero EOUT_F)

/-- One `q` iteration: pop the halt bit, emit `sig+1` patterns if it is set,
then advance the head-cell base by `1^(sig+1)`. -/
private def finBody : Cmd :=
  Cmd.op (.head EE ED) ;; Cmd.op (.tail ED ED) ;;
  Cmd.ifBit EE (Cmd.forBnd EJ2 EA finInner) enop ;;
  FrontPieces.tallyReg EJ3 EA EC

/-- **Stage F.** `EOUT_F := encFinal (flattenFinal (guessFinal M))`. -/
def stageFin : Cmd := finPre ;; Cmd.forBnd EJ1 EB finBody

private theorem finPre_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf) :
    State.get (finPre.eval s) EOUT_F = []
    ∧ State.get (finPre.eval s) EA = List.replicate (M.sig + 1) 1
    ∧ State.get (finPre.eval s) EB = List.replicate (M.states + 1) 1
    ∧ State.get (finPre.eval s) EC = List.replicate (M.sig + 1) 1
    ∧ State.get (finPre.eval s) ED = M.halt.map S1Parse.bitOf
    ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EA → r ≠ EB → r ≠ EC → r ≠ ED →
        State.get (finPre.eval s) r = State.get s r) := by
  simp only [finPre, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [hsig, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [hst, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [hsig, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    exact hph
  · intro r h1 h2 h3 h4 h5
    repeat first
      | rw [State.get_set_ne _ _ _ _ h1]
      | rw [State.get_set_ne _ _ _ _ h2]
      | rw [State.get_set_ne _ _ _ _ h3]
      | rw [State.get_set_ne _ _ _ _ h4]
      | rw [State.get_set_ne _ _ _ _ h5]

/-- The inner `b`-loop: `sig+1` singleton patterns for one halting state `q`. -/
private theorem finLoopB_run (sig q : Nat) (w : State) (pre : List Nat)
    (hOut : State.get w EOUT_F = pre)
    (hEA : State.get w EA = List.replicate (sig + 1) 1)
    (hEC : State.get w EC = List.replicate ((sig + 1) * (q + 1)) 1) :
    State.get ((Cmd.forBnd EJ2 EA finInner).eval w) EOUT_F
        = pre ++ FlatTCCFree.encFinal
            ((List.range (sig + 1)).map (fun b => [S1Cards.hv sig q b]))
    ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EJ2 → r ≠ EJ3 →
        State.get ((Cmd.forBnd EJ2 EA finInner).eval w) r = State.get w r) := by
  set MI : Nat → State → Prop := fun i t =>
    State.get t EOUT_F
        = pre ++ FlatTCCFree.encFinal ((List.range i).map (fun b => [S1Cards.hv sig q b]))
      ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EJ2 → r ≠ EJ3 → State.get t r = State.get w r)
    with hMI
  have h0 : MI 0 w := ⟨by rw [hOut]; simp [FlatTCCFree.encFinal], fun _ _ _ _ => rfl⟩
  have hstep : ∀ i t, i < (State.get w EA).length → MI i t →
      MI (i + 1) (finInner.eval (t.set EJ2 (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨hO, hFr⟩ := hM
    set t0 := t.set EJ2 (List.replicate i 1) with ht0
    have h0O : State.get t0 EOUT_F
        = pre ++ FlatTCCFree.encFinal
            ((List.range i).map (fun b => [S1Cards.hv sig q b])) := by
      rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EOUT_F : Var) ≠ EJ2)]; exact hO
    have h0C : State.get t0 EC = List.replicate ((sig + 1) * (q + 1)) 1 := by
      rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EC : Var) ≠ EJ2),
        hFr EC (by decide) (by decide) (by decide)]
      exact hEC
    have h0J : State.get t0 EJ2 = List.replicate i 1 := by
      rw [ht0, State.get_set_eq]
    have h0Fr : ∀ r : Var, r ≠ EOUT_F → r ≠ EJ2 → r ≠ EJ3 →
        State.get t0 r = State.get w r := by
      intro r a b c; rw [ht0, State.get_set_ne _ _ _ _ b]; exact hFr r a b c
    clear_value t0
    -- peel the five commands of `finInner`
    set a1 := (Cmd.op (.appendOne EOUT_F)).eval t0 with ha1
    have h1O : State.get a1 EOUT_F = State.get t0 EOUT_F ++ [1] := by
      rw [ha1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
    have h1Fr : ∀ r : Var, r ≠ EOUT_F → State.get a1 r = State.get t0 r := by
      intro r hr; rw [ha1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value a1
    obtain ⟨h2O, h2Fr, -⟩ := FrontPieces.tallyReg_run EJ3 EC EOUT_F a1 (by decide)
    set a2 := (FrontPieces.tallyReg EJ3 EC EOUT_F).eval a1 with ha2
    clear_value a2
    obtain ⟨h3O, h3Fr, -⟩ := FrontPieces.tallyReg_run EJ3 EJ2 EOUT_F a2 (by decide)
    set a3 := (FrontPieces.tallyReg EJ3 EJ2 EOUT_F).eval a2 with ha3
    clear_value a3
    set a4 := (Cmd.op (.appendZero EOUT_F)).eval a3 with ha4
    have h4O : State.get a4 EOUT_F = State.get a3 EOUT_F ++ [0] := by
      rw [ha4, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
    have h4Fr : ∀ r : Var, r ≠ EOUT_F → State.get a4 r = State.get a3 r := by
      intro r hr; rw [ha4, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value a4
    set a5 := (Cmd.op (.appendZero EOUT_F)).eval a4 with ha5
    have h5O : State.get a5 EOUT_F = State.get a4 EOUT_F ++ [0] := by
      rw [ha5, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
    have h5Fr : ∀ r : Var, r ≠ EOUT_F → State.get a5 r = State.get a4 r := by
      intro r hr; rw [ha5, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value a5
    have hev : finInner.eval t0 = a5 := by
      rw [ha5, ha4, ha3, ha2, ha1]
      unfold finInner
      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    -- the two source registers survive to their reads
    have h1C : State.get a1 EC = List.replicate ((sig + 1) * (q + 1)) 1 := by
      rw [h1Fr EC (by decide)]; exact h0C
    have h2J : State.get a2 EJ2 = List.replicate i 1 := by
      rw [h2Fr EJ2 (by decide) (by decide), h1Fr EJ2 (by decide)]; exact h0J
    refine ⟨?_, ?_⟩
    · rw [hev, h5O, h4O, h3O, h2O, h1O, h1C, h2J, h0O]
      simp only [List.length_replicate, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, encFinal_append, encFinal_singleton,
        show S1Cards.hv sig q i = (sig + 1) * (q + 1) + i from rfl, List.replicate_add]
      simp [List.append_assoc]
    · intro r b1 b2 b3
      rw [hev, h5Fr r b1, h4Fr r b1, h3Fr r b1 b3, h2Fr r b1 b3, h1Fr r b1]
      exact h0Fr r b1 b2 b3
  have key := Cmd.foldlState_range_induct finInner EJ2 (State.get w EA).length w MI h0 hstep
  rw [Cmd.eval_forBnd]
  rw [hEA, List.length_replicate] at key
  rw [hEA, List.length_replicate]
  exact key

private theorem drop_getElem_cons {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = (l[i]'hi) :: l.drop (i + 1) := List.drop_eq_getElem_cons hi

private theorem tail_drop_succ {α : Type} (l : List α) (i : Nat) :
    (l.drop i).tail = l.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, Nat.add_comm]

private theorem getD_of_le {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The pattern block contributed by state `q`. -/
private def finRow (sig : Nat) (hb : List Nat) (q : Nat) : List (List Nat) :=
  if S1Cards.haltBit hb q then
    (List.range (sig + 1)).map (fun b => [S1Cards.hv sig q b])
  else []

private theorem finBlocks_range (sig states : Nat) (hb : List Nat) :
    finBlocks sig states hb = (List.range (states + 1)).flatMap (finRow sig hb) := rfl

/-- One `q` iteration of stage F. -/
private theorem finBody_step (sig : Nat) (hb : List Nat) (u : State) (i : Nat) (t : State)
    (hO : State.get t EOUT_F
        = FlatTCCFree.encFinal ((List.range i).flatMap (finRow sig hb)))
    (hC : State.get t EC = List.replicate ((sig + 1) * (i + 1)) 1)
    (hD : State.get t ED = hb.drop i)
    (hFr : ∀ r : Var, r ≠ EOUT_F → r ≠ EC → r ≠ ED → r ≠ EE → r ≠ EJ1 → r ≠ EJ2 →
        r ≠ EJ3 → r ≠ EK1 → State.get t r = State.get u r)
    (hA : State.get u EA = List.replicate (sig + 1) 1) :
    State.get (finBody.eval (t.set EJ1 (List.replicate i 1))) EOUT_F
        = FlatTCCFree.encFinal ((List.range (i + 1)).flatMap (finRow sig hb))
    ∧ State.get (finBody.eval (t.set EJ1 (List.replicate i 1))) EC
        = List.replicate ((sig + 1) * (i + 2)) 1
    ∧ State.get (finBody.eval (t.set EJ1 (List.replicate i 1))) ED = hb.drop (i + 1)
    ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EC → r ≠ ED → r ≠ EE → r ≠ EJ1 → r ≠ EJ2 →
        r ≠ EJ3 → r ≠ EK1 →
        State.get (finBody.eval (t.set EJ1 (List.replicate i 1))) r = State.get u r) := by
  set t0 := t.set EJ1 (List.replicate i 1) with ht0
  have g0O : State.get t0 EOUT_F
      = FlatTCCFree.encFinal ((List.range i).flatMap (finRow sig hb)) := by
    rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EOUT_F : Var) ≠ EJ1)]; exact hO
  have g0C : State.get t0 EC = List.replicate ((sig + 1) * (i + 1)) 1 := by
    rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EC : Var) ≠ EJ1)]; exact hC
  have g0D : State.get t0 ED = hb.drop i := by
    rw [ht0, State.get_set_ne _ _ _ _ (by decide : (ED : Var) ≠ EJ1)]; exact hD
  have g0A : State.get t0 EA = List.replicate (sig + 1) 1 := by
    rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EA : Var) ≠ EJ1),
      hFr EA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hA
  have g0Fr : ∀ r : Var, r ≠ EOUT_F → r ≠ EC → r ≠ ED → r ≠ EE → r ≠ EJ1 → r ≠ EJ2 →
      r ≠ EJ3 → r ≠ EK1 → State.get t0 r = State.get u r := by
    intro r b1 b2 b3 b4 b5 b6 b7 b8
    rw [ht0, State.get_set_ne _ _ _ _ b5]; exact hFr r b1 b2 b3 b4 b5 b6 b7 b8
  clear_value t0
  -- pop the halt bit
  set v1 := (Cmd.op (.head EE ED)).eval t0 with hv1
  have h1E : State.get v1 EE = (match hb.drop i with | [] => [] | x :: _ => [x]) := by
    rw [hv1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, g0D]; rfl
  have h1Fr : ∀ r : Var, r ≠ EE → State.get v1 r = State.get t0 r := by
    intro r hr; rw [hv1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value v1
  set v2 := (Cmd.op (.tail ED ED)).eval v1 with hv2
  have h2D : State.get v2 ED = (hb.drop i).tail := by
    rw [hv2, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, h1Fr ED (by decide), g0D]
  have h2Fr : ∀ r : Var, r ≠ ED → State.get v2 r = State.get v1 r := by
    intro r hr; rw [hv2, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value v2
  have h2E : State.get v2 EE = (match hb.drop i with | [] => [] | x :: _ => [x]) := by
    rw [h2Fr EE (by decide)]; exact h1E
  have h2O : State.get v2 EOUT_F
      = FlatTCCFree.encFinal ((List.range i).flatMap (finRow sig hb)) := by
    rw [h2Fr EOUT_F (by decide), h1Fr EOUT_F (by decide)]; exact g0O
  have h2C : State.get v2 EC = List.replicate ((sig + 1) * (i + 1)) 1 := by
    rw [h2Fr EC (by decide), h1Fr EC (by decide)]; exact g0C
  have h2A : State.get v2 EA = List.replicate (sig + 1) 1 := by
    rw [h2Fr EA (by decide), h1Fr EA (by decide)]; exact g0A
  have h2G : ∀ r : Var, r ≠ EOUT_F → r ≠ EC → r ≠ ED → r ≠ EE → r ≠ EJ1 → r ≠ EJ2 →
      r ≠ EJ3 → r ≠ EK1 → State.get v2 r = State.get u r := by
    intro r b1 b2 b3 b4 b5 b6 b7 b8
    rw [h2Fr r b3, h1Fr r b4]; exact g0Fr r b1 b2 b3 b4 b5 b6 b7 b8
  -- the branch
  set v3 := (Cmd.ifBit EE (Cmd.forBnd EJ2 EA finInner) enop).eval v2 with hv3
  have hbranch : State.get v3 EOUT_F
        = FlatTCCFree.encFinal ((List.range i).flatMap (finRow sig hb)
            ++ finRow sig hb i)
      ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EJ2 → r ≠ EJ3 → r ≠ EK1 →
          State.get v3 r = State.get v2 r) := by
    by_cases hi : i < hb.length
    · rw [drop_getElem_cons hb i hi] at h2E
      by_cases hx : hb[i]'hi = 1
      · have hrow : finRow sig hb i
            = (List.range (sig + 1)).map (fun b => [S1Cards.hv sig i b]) := by
          unfold finRow S1Cards.haltBit
          rw [if_pos (show decide (hb.getD i 0 = 1) = true by
            rw [List.getD_eq_getElem _ _ hi, hx]; rfl)]
        have htest : State.get v2 EE = [1] := by rw [h2E, hx]
        obtain ⟨hIn, hInFr⟩ := finLoopB_run sig i v2 _ h2O h2A h2C
        refine ⟨?_, ?_⟩
        · rw [hv3, Cmd.eval_ifBit_true _ _ _ _ htest, hIn, hrow, encFinal_append]
        · intro r b1 b2 b3 _
          rw [hv3, Cmd.eval_ifBit_true _ _ _ _ htest]; exact hInFr r b1 b2 b3
      · have hrow : finRow sig hb i = [] := by
          unfold finRow S1Cards.haltBit
          rw [if_neg (by rw [List.getD_eq_getElem _ _ hi]; simpa using hx)]
        have htest : State.get v2 EE ≠ [1] := by
          rw [h2E]; simpa using hx
        refine ⟨?_, ?_⟩
        · rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest]
          unfold enop
          rw [Cmd.eval_op]
          simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (EOUT_F : Var) ≠ EK1)]
          rw [h2O, hrow, List.append_nil]
        · intro r b1 b2 b3 b4
          rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest]
          unfold enop
          rw [Cmd.eval_op]
          exact State.get_set_ne _ _ _ _ b4
    · have hd : hb.drop i = [] := List.drop_eq_nil_of_le (Nat.le_of_not_lt hi)
      rw [hd] at h2E
      have hrow : finRow sig hb i = [] := by
        unfold finRow S1Cards.haltBit
        rw [if_neg (by rw [getD_of_le _ _ _ (Nat.le_of_not_lt hi)]; decide)]
      have htest : State.get v2 EE ≠ [1] := by rw [h2E]; decide
      refine ⟨?_, ?_⟩
      · rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest]
        unfold enop
        rw [Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (EOUT_F : Var) ≠ EK1)]
        rw [h2O, hrow, List.append_nil]
      · intro r b1 b2 b3 b4
        rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest]
        unfold enop
        rw [Cmd.eval_op]
        exact State.get_set_ne _ _ _ _ b4
  obtain ⟨h3O, h3Fr⟩ := hbranch
  clear_value v3
  have h3C : State.get v3 EC = List.replicate ((sig + 1) * (i + 1)) 1 := by
    rw [h3Fr EC (by decide) (by decide) (by decide) (by decide)]; exact h2C
  have h3A : State.get v3 EA = List.replicate (sig + 1) 1 := by
    rw [h3Fr EA (by decide) (by decide) (by decide) (by decide)]; exact h2A
  have h3D : State.get v3 ED = (hb.drop i).tail := by
    rw [h3Fr ED (by decide) (by decide) (by decide) (by decide)]; exact h2D
  -- advance the head-cell base
  obtain ⟨h4C, h4Fr, -⟩ := FrontPieces.tallyReg_run EJ3 EA EC v3 (by decide)
  have hev : finBody.eval t0
      = (FrontPieces.tallyReg EJ3 EA EC).eval v3 := by
    rw [hv3, hv2, hv1]
    unfold finBody
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hev, h4Fr EOUT_F (by decide) (by decide), h3O, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · have harith : (sig + 1) * (i + 1) + (sig + 1) = (sig + 1) * (i + 2) := by ring
    rw [hev, h4C, h3C, h3A, List.length_replicate, ← List.replicate_add, harith]
  · rw [hev, h4Fr ED (by decide) (by decide), h3D, tail_drop_succ]
  · intro r b1 b2 b3 b4 b5 b6 b7 b8
    rw [hev, h4Fr r b2 b7, h3Fr r b1 b6 b7 b8]
    exact h2G r b1 b2 b3 b4 b5 b6 b7 b8

/-- **Stage F is correct.** The final register holds the guess tableau's own
`final` stream. No validity hypothesis: the halt-bit drain reproduces
`M.halt.getD` out of range too (finding 1). -/
theorem stageFin_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf) :
    State.get (stageFin.eval s) EOUT_F
        = FlatTCCFree.encFinal (FlatTCC.flattenFinal (guessFinal M))
    ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EA → r ≠ EB → r ≠ EC → r ≠ ED → r ≠ EE →
        r ≠ EJ1 → r ≠ EJ2 → r ≠ EJ3 → r ≠ EK1 →
        State.get (stageFin.eval s) r = State.get s r) := by
  obtain ⟨p0, pA, pB, pC, pD, pFr⟩ := finPre_run M s hsig hst hph
  set u := finPre.eval s with hu
  clear_value u
  set hb := M.halt.map S1Parse.bitOf with hhb
  set MO : Nat → State → Prop := fun i t =>
    State.get t EOUT_F = FlatTCCFree.encFinal ((List.range i).flatMap (finRow M.sig hb))
    ∧ State.get t EC = List.replicate ((M.sig + 1) * (i + 1)) 1
    ∧ State.get t ED = hb.drop i
    ∧ (∀ r : Var, r ≠ EOUT_F → r ≠ EC → r ≠ ED → r ≠ EE → r ≠ EJ1 → r ≠ EJ2 →
        r ≠ EJ3 → r ≠ EK1 → State.get t r = State.get u r) with hMO
  have h0 : MO 0 u := by
    refine ⟨by rw [p0]; rfl, by rw [pC, Nat.mul_one], by rw [pD, List.drop_zero], fun _ _ _ _ _ _ _ _ _ => rfl⟩
  have hstep : ∀ i t, i < (State.get u EB).length → MO i t →
      MO (i + 1) (finBody.eval (t.set EJ1 (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨a, b, c, d⟩ := hM
    exact finBody_step M.sig hb u i t a b c d pA
  have key := Cmd.foldlState_range_induct finBody EJ1 (State.get u EB).length u MO h0 hstep
  rw [pB, List.length_replicate] at key
  obtain ⟨kO, -, -, kFr⟩ := key
  have hev : stageFin.eval s = Cmd.foldlState finBody EJ1
      (List.range (M.states + 1)) u := by
    unfold stageFin
    rw [Cmd.eval_seq, ← hu, Cmd.eval_forBnd, pB, List.length_replicate]
  refine ⟨?_, ?_⟩
  · rw [hev, kO, finBlocks_eq M, finBlocks_range]
  · intro r b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
    rw [hev, kFr r b1 b4 b5 b6 b7 b8 b9 b10]
    exact pFr r b1 b2 b3 b4 b5

theorem stageFin_usesBelow : Cmd.UsesBelow stageFin 48 := by
  simp [stageFin, finPre, finBody, finInner, enop, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow, EOUT_F, EA, EB, EC, ED, EE, EJ1, EJ2, EJ3, EK1,
    S1Parse.PSIG, S1Parse.PSTATES, S1Parse.PHALT]

end S1Emit
