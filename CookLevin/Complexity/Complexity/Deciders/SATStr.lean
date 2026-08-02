import Complexity.Complexity.Deciders.EvalCnfSplit
import Complexity.Complexity.Deciders.CnfWellFormed
import Complexity.Lang.HardnessStr
import Complexity.Lang.SerializeStr

set_option autoImplicit false
set_option linter.dupNamespace false

/-! # `SATStr` — SAT as a STRING language, with an `InNPWitnessStr`

Bottom-up item 2. `CookLevinHonest.CookLevinStr : NPcompleteStr SAT` quantifies
over `Q : List Bool → Prop` presented with a real `Cmd` verifier reading the raw
string in the canonical one-register layout. `Complexity/NonVacuity.lean` showed
that class is inhabited — by `SquareStr`, which is in **P**. This file puts an
**NP-complete** language in it:

```
SATStr x  :=  SAT (parseTotal (strBits x))
          ↔  ∃ N, strBits x = encodeCnf N ∧ SAT N        (satStr_iff)
```

— "the bits of `x` are the canonical encoding of a satisfiable CNF".

## What the machine actually owes (the finding this file rests on)

The HANDOFF scoped this as "an on-machine parser `Cmd` from a self-delimiting
bit format into the twelve-register layout". **It is not.** The development's
canonical CNF encoding `EvalCnfCmd.encodeCnf` is *already* a flat `0`/`1` cell
stream, and the canonical string layout `certState x` is *already* one register
of `0`/`1` cells. So `CNF_STREAM` is a **copy of the input register**, and the
only field of `EvalCnfCmd.encodeState` the raw string does not carry is
`CLAUSE_TALLY = 1^|N|`.

The re-encoder is therefore a **single left-to-right scan** that
(a) validates the stream against the grammar and (b) counts the clauses — the
four-state DFA of `Complexity/Complexity/Deciders/CnfWellFormed.lean`, one
`forBnd` with two flag registers and a tally. `scanBody` is 11 ops.

A malformed stream is not rejected by a separate mechanism: the builder
overwrites the layout with `encodeCnf [[]] = [0]` (one empty clause,
unsatisfiable), which is exactly the value `CnfWellFormed.parseTotal` gives it.
"Not an encoding" and "unsatisfiable" are the same verdict, so one verifier
decides both — see `not_sat_botCnf`.

The certificate half is **reused verbatim**: `EvalCnfSplit.certDecode` and its
proven bridge. The builder leaves registers `16`–`18` (its scratch) untouched
and hands it exactly `EvalCnfSplit.satEIn (cnfOf x, c)`, so `Cmd.eval_agree`
pushes that bridge through with no new register work.

## The register frame

```
0  input bits x → OUTPUT       16–18  certDecode's scratch (untouched here)
1  cert bits c  → CLAUSE_TALLY 19 WCUR  the scan cursor
2  CNF_STREAM                  20 WIDX  the forBnd counter
3  ASSGN (the cert bits)       21 WHD   head cell / branch flag
4–15 the verifier's scratch    22 WSA   DFA `inLit`
                               23 WSB   DFA `pending`
                               24 WTAL  the clause tally, 1^k
```

`satStrMfc` uses registers below `25`; the verifier's frame is `16`, so
everything from `16` up is invisible to the bridge (FINDING AE).

Probe: `probes/SATStrProbe.lean` — the loop invariant at every index, the bridge
at every input of length `≤ 7`, and machine-vs-model agreement exhaustively at
length `≤ 6`.
-/

namespace SATStr

open Complexity.Lang EvalCnfCmd CnfWellFormed

/-! ## The language -/

/-! `strBits` — the machine's view of a bit string, one `0`/`1` cell per bit —
lives in `Lang/SerializeStr.lean` together with `certState_eq_strBits`,
`strBits_length`, `strBits_bit` and the `Serialize (List Bool)` instance it is
the encoder of. It used to be defined here; it was hoisted on 2026-08-05 so
that the chain-head layout (`certState`) and the chain-*end* serialization of a
bit string are the same function and not two readings. -/

/-- The CNF a bit string denotes: the canonical parse where the string is an
encoding, the unsatisfiable `[[]]` where it is not. -/
def cnfOf (x : List Bool) : cnf := parseTotal (strBits x)

/-- **SAT as a language of bit strings.** -/
def SATStr (x : List Bool) : Prop := SAT (cnfOf x)

/-- **What the language says, in the form a reader should check.** `SATStr` is
exactly "the bits of `x` spell out a satisfiable CNF" — the junk branch is not a
loophole, because `[[]]` is unsatisfiable. -/
theorem satStr_iff (x : List Bool) :
    SATStr x ↔ ∃ N : cnf, strBits x = encodeCnf N ∧ SAT N := by
  constructor
  · intro h
    by_cases hwf : wfCnfB (strBits x) = true
    · exact ⟨cnfOf x, (encodeCnf_parseTotal _ (strBits_bit x) hwf).symm, h⟩
    · have hb : cnfOf x = botCnf :=
        parseTotal_of_not_wf _ (by simpa using hwf)
      exact absurd (hb ▸ h) not_sat_botCnf
  · rintro ⟨N, hN, hsat⟩
    show SAT (parseTotal (strBits x))
    rw [hN, parseTotal_encodeCnf N]
    exact hsat

/-- The language is a real one: `[]` is `encodeCnf []`, the empty CNF, which is
satisfiable. -/
theorem satStr_nil : SATStr [] := by
  refine (satStr_iff []).mpr ⟨[], rfl, ⟨[], rfl⟩⟩

/-- `[false]` is `encodeCnf [[]]` — one empty clause. -/
theorem not_satStr_false : ¬ SATStr [false] := by
  intro h
  obtain ⟨N, hN, hsat⟩ := (satStr_iff _).mp h
  have : N = botCnf := by
    have := parseTotal_encodeCnf N
    rw [← hN] at this
    exact this.symm.trans (by rfl)
  exact absurd (this ▸ hsat) not_sat_botCnf

/-- `[true]` is not an encoding at all — the scanner's `pending` bit is what
rules it out. -/
theorem not_satStr_true : ¬ SATStr [true] := by
  intro h
  obtain ⟨N, hN, -⟩ := (satStr_iff _).mp h
  have hwf : wfCnfB (strBits [true]) = true := by
    rw [hN]; exact wfCnfB_encodeCnf N
  exact absurd hwf (by decide)

/-- `encodeCnf [[(true, 0)]]` — the one-literal formula `x₀`. -/
theorem satStr_x0 : SATStr [true, true, false, false] :=
  (satStr_iff _).mpr ⟨[[(true, 0)]], rfl, ⟨[0], by show evalCnf [0] [[(true, 0)]] = true; rfl⟩⟩

/-- `encodeCnf [[(true,0)], [(false,0)]]` — `x₀ ∧ ¬x₀`, an encoding of an
UNSATISFIABLE formula. Together with `satStr_x0` this separates "is an encoding"
from "is in the language". -/
theorem not_satStr_x0_and_not_x0 :
    ¬ SATStr [true, true, false, false, true, false, false, false] := by
  intro h
  obtain ⟨N, hN, hsat⟩ := (satStr_iff _).mp h
  have hNe : N = [[(true, 0)], [(false, 0)]] := by
    have h1 : parseTotal (strBits [true, true, false, false, true, false, false, false])
        = N := by rw [hN, parseTotal_encodeCnf]
    rw [← h1]; rfl
  subst hNe
  obtain ⟨a, ha⟩ := hsat
  have : evalCnf a [[(true, 0)], [(false, 0)]] = true := ha
  simp only [evalCnf, evalClause, evalLiteral, List.all_cons, List.any_cons,
    List.any_nil, List.all_nil] at this
  rcases hv : evalVar a 0 <;> simp [hv] at this

/-! ## The registers -/

/-- The scan cursor over the input bits. -/
def WCUR : Var := 19
/-- The scan loop's `forBnd` counter. -/
def WIDX : Var := 20
/-- Head cell, then the well-formedness branch flag. -/
def WHD : Var := 21
/-- DFA flag `inLit`: `[1]` inside a literal, `[]` at a literal slot. -/
def WSA : Var := 22
/-- DFA flag `pending`: `[1]` when a clause is open. -/
def WSB : Var := 23
/-- The clause tally, `1^k`. -/
def WTAL : Var := 24

/-- A DFA flag as register content. -/
def flagOf (b : Bool) : List Nat := if b then [1] else []

theorem flagOf_true : flagOf true = [1] := rfl
theorem flagOf_false : flagOf false = [] := rfl

/-! ## The program -/

/-- **One cell of the scan** — `CnfWellFormed.scanStep`, transcribed. The three
`ifBit`s are, outside in: `inLit?`, then `pending?` (or the cell), then the
cell. The `clear WHD` arms are the layer's cheap no-op; `WHD` is rewritten at
the top of every iteration. -/
def scanBody : Cmd :=
  Cmd.op (.head WHD WCUR) ;;
  Cmd.op (.tail WCUR WCUR) ;;
  Cmd.ifBit WSA
    (Cmd.ifBit WSB
      (Cmd.ifBit WHD
        (Cmd.op (.clear WHD))
        (Cmd.op (.clear WSA)))
      (Cmd.op (.clear WSB) ;; Cmd.op (.appendOne WSB)))
    (Cmd.ifBit WHD
      (Cmd.op (.clear WSA) ;; Cmd.op (.appendOne WSA) ;; Cmd.op (.clear WSB))
      (Cmd.op (.clear WSB) ;; Cmd.op (.appendOne WTAL)))

/-- The prologue: certificate bits to `ASSGN`, input bits to the cursor, scan
state zeroed. -/
def satStrPre : Cmd :=
  Cmd.op (.copy ASSGN 1) ;;
  Cmd.op (.copy WCUR 0) ;;
  Cmd.op (.clear WSA) ;;
  Cmd.op (.clear WSB) ;;
  Cmd.op (.clear WTAL)

/-- The malformed branch: `encodeCnf [[]] = [0]` with its tally `1^1`. -/
def badBranch : Cmd :=
  Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM) ;;
  Cmd.op (.clear CLAUSE_TALLY) ;; Cmd.op (.appendOne CLAUSE_TALLY)

/-- Lay the verifier's registers from the scan's results. -/
def satStrPostA : Cmd :=
  Cmd.op (.copy CNF_STREAM 0) ;;
  Cmd.op (.copy CLAUSE_TALLY WTAL) ;;
  Cmd.op (.clear OUTPUT) ;;
  Cmd.op (.nonEmpty WHD WSA)

/-- …then override them if the scan did not end in the accepting state. -/
def satStrPostB : Cmd :=
  Cmd.ifBit WHD badBranch
    (Cmd.op (.nonEmpty WHD WSB) ;; Cmd.ifBit WHD badBranch (Cmd.op (.clear WHD)))

/-- **The builder**: scan once, lay the layout, fix up the malformed branch. -/
def satStrBuild : Cmd :=
  satStrPre ;; (Cmd.forBnd WIDX WCUR scanBody ;; (satStrPostA ;; satStrPostB))

/-- **The re-encoder**: the builder, then `EvalCnfSplit.certDecode` verbatim. -/
def satStrMfc : Cmd := satStrBuild ;; EvalCnfSplit.certDecode

/-- The composite verifier's input layout — the canonical string one. -/
def strEIn (v : List Bool × List Bool) : State := certState v.1 ++ certState v.2

theorem strEIn_lit (x c : List Bool) : strEIn (x, c) = [strBits x, strBits c] := rfl

theorem strEIn_get0 (x c : List Bool) : State.get (strEIn (x, c)) 0 = strBits x := rfl
theorem strEIn_get1 (x c : List Bool) : State.get (strEIn (x, c)) 1 = strBits c := rfl

theorem strEIn_size (x c : List Bool) :
    State.size (strEIn (x, c)) = x.length + c.length := by
  show State.size [strBits x, strBits c] = _
  simp [State.size, strBits_length]

theorem strEIn_bit (v : List Bool × List Bool) : Compile.BitState (strEIn v) := by
  rcases v with ⟨x, c⟩
  rw [strEIn_lit]
  intro reg hreg z hz
  have : reg = strBits x ∨ reg = strBits c := by
    simpa using hreg
  rcases this with rfl | rfl
  · exact strBits_bit x z hz
  · exact strBits_bit c z hz

/-! ## The scan loop

`scanTake l i` is the model after `i` cells; the invariant is
`WCUR = l.drop i`, the two flags, and the tally — exactly what
`probes/SATStrProbe.lean` §7 `#eval`s at every index. -/

/-- The scanner's state after the first `i` cells. -/
def scanTake (l : List Nat) (i : Nat) : Bool × Bool × Nat :=
  (l.take i).foldl scanStep (false, false, 0)

theorem scanTake_zero (l : List Nat) : scanTake l 0 = (false, false, 0) := rfl

theorem scanTake_length (l : List Nat) : scanTake l l.length = scanRun l := by
  rw [scanTake, List.take_length]; rfl

theorem scanTake_succ (l : List Nat) (i : Nat) (hi : i < l.length) :
    scanTake l (i + 1) = scanStep (scanTake l i) l[i] := by
  rw [scanTake, scanTake, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **One iteration of the scan.** Given the invariant at `i` (the counter is
irrelevant to this body), `scanBody` establishes it at `i + 1`. Only the four
scan registers are constrained — the frame is the write-set lemma's job
(FINDING AH). -/
theorem scanBody_run (l : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hC : State.get s WCUR = l.drop i)
    (hA : State.get s WSA = flagOf (scanTake l i).1)
    (hB : State.get s WSB = flagOf (scanTake l i).2.1)
    (hT : State.get s WTAL = List.replicate (scanTake l i).2.2 1) :
    State.get (scanBody.eval s) WCUR = l.drop (i + 1)
      ∧ State.get (scanBody.eval s) WSA = flagOf (scanTake l (i + 1)).1
      ∧ State.get (scanBody.eval s) WSB = flagOf (scanTake l (i + 1)).2.1
      ∧ State.get (scanBody.eval s) WTAL = List.replicate (scanTake l (i + 1)).2.2 1 := by
  have hcons : State.get s WCUR = l[i] :: l.drop (i + 1) := by
    rw [hC, List.drop_eq_getElem_cons hi]
  -- pop one cell
  have e1 : (Cmd.op (Op.head WHD WCUR)).eval s = s.set WHD [l[i]] := by
    simp only [Cmd.eval_op, Op.eval, hcons]
  have hC1 : State.get (s.set WHD [l[i]]) WCUR = l[i] :: l.drop (i + 1) := by
    rw [State.get_set_ne s WHD _ WCUR (by decide)]; exact hcons
  have e2 : (Cmd.op (Op.tail WCUR WCUR)).eval (s.set WHD [l[i]])
      = (s.set WHD [l[i]]).set WCUR (l.drop (i + 1)) := by
    simp only [Cmd.eval_op, Op.eval, hC1, List.tail_cons]
  rw [scanBody, Cmd.eval_seq, e1, Cmd.eval_seq, e2]
  set t : State := (s.set WHD [l[i]]).set WCUR (l.drop (i + 1)) with ht
  have hT_C : State.get t WCUR = l.drop (i + 1) := State.get_set_eq _ _ _
  have hT_HD : State.get t WHD = [l[i]] := by
    rw [ht, State.get_set_ne _ WCUR _ WHD (by decide)]
    exact State.get_set_eq _ _ _
  have hT_A : State.get t WSA = flagOf (scanTake l i).1 := by
    rw [ht, State.get_set_ne _ WCUR _ WSA (by decide),
      State.get_set_ne _ WHD _ WSA (by decide)]
    exact hA
  have hT_B : State.get t WSB = flagOf (scanTake l i).2.1 := by
    rw [ht, State.get_set_ne _ WCUR _ WSB (by decide),
      State.get_set_ne _ WHD _ WSB (by decide)]
    exact hB
  have hT_T : State.get t WTAL = List.replicate (scanTake l i).2.2 1 := by
    rw [ht, State.get_set_ne _ WCUR _ WTAL (by decide),
      State.get_set_ne _ WHD _ WTAL (by decide)]
    exact hT
  rw [scanTake_succ l i hi]
  -- the model's three cases
  rcases hm : scanTake l i with ⟨a, b, k⟩
  rw [hm] at hT_A hT_B hT_T
  by_cases hcell : l[i] = 1
  · -- cell is `1`
    have hHD : State.get t WHD = [1] := by rw [hT_HD, hcell]
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl),
              Cmd.eval_ifBit_true _ _ _ _ hHD]
            simp only [Cmd.eval_op, Op.eval, scanStep, hcell, if_pos]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ WHD _ WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ WHD _ WSA (by decide)]; exact hT_A
            · rw [State.get_set_ne _ WHD _ WSB (by decide)]; exact hT_B
            · rw [State.get_set_ne _ WHD _ WTAL (by decide)]; exact hT_T
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [flagOf])]
            simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
              State.set_set, scanStep]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ WSB _ WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ WSB _ WSA (by decide)]; exact hT_A
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [flagOf]
            · rw [State.get_set_ne _ WSB _ WTAL (by decide)]; exact hT_T
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [flagOf]),
          Cmd.eval_ifBit_true _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
          State.set_set, scanStep, hcell, if_pos]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WSB _ WCUR (by decide),
            State.get_set_ne _ WSA _ WCUR (by decide)]
          exact hT_C
        · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]; rfl
        · first | rfl | (rw [State.get_set_eq]; rfl) | simp [flagOf]
        · rw [State.get_set_ne _ WSB _ WTAL (by decide),
            State.get_set_ne _ WSA _ WTAL (by decide)]
          exact hT_T
  · -- cell is not `1`
    have hHD : State.get t WHD ≠ [1] := by
      rw [hT_HD]; simpa using hcell
    cases a with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
        cases b with
        | true =>
            rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl),
              Cmd.eval_ifBit_false _ _ _ _ hHD]
            simp only [Cmd.eval_op, Op.eval, scanStep, if_neg hcell]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ WSA _ WCUR (by decide)]; exact hT_C
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [flagOf]
            · rw [State.get_set_ne _ WSA _ WSB (by decide)]; exact hT_B
            · rw [State.get_set_ne _ WSA _ WTAL (by decide)]; exact hT_T
        | false =>
            rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [flagOf])]
            simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
              State.set_set, scanStep]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [State.get_set_ne _ WSB _ WCUR (by decide)]; exact hT_C
            · rw [State.get_set_ne _ WSB _ WSA (by decide)]; exact hT_A
            · first | rfl | (rw [State.get_set_eq]; rfl) | simp [flagOf]
            · rw [State.get_set_ne _ WSB _ WTAL (by decide)]; exact hT_T
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [flagOf]),
          Cmd.eval_ifBit_false _ _ _ _ hHD]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
          State.set_set, scanStep, if_neg hcell]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WTAL _ WCUR (by decide),
            State.get_set_ne _ WSB _ WCUR (by decide)]
          exact hT_C
        · rw [State.get_set_ne _ WTAL _ WSA (by decide),
            State.get_set_ne _ WSB _ WSA (by decide)]
          exact hT_A
        · rw [State.get_set_ne _ WTAL _ WSB (by decide), State.get_set_eq]; rfl
        · rw [State.get_set_ne _ WSB _ WTAL (by decide), hT_T, ← List.replicate_succ']

/-- **The whole scan.** From a zeroed scan frame with the stream on the cursor,
the loop leaves the DFA's final state in the two flags and the clause count in
the tally. -/
theorem scanLoop_run (l : List Nat) (s : State)
    (hC : State.get s WCUR = l) (hA : State.get s WSA = [])
    (hB : State.get s WSB = []) (hT : State.get s WTAL = []) :
    State.get ((Cmd.forBnd WIDX WCUR scanBody).eval s) WSA = flagOf (scanRun l).1
      ∧ State.get ((Cmd.forBnd WIDX WCUR scanBody).eval s) WSB = flagOf (scanRun l).2.1
      ∧ State.get ((Cmd.forBnd WIDX WCUR scanBody).eval s) WTAL
          = List.replicate (scanRun l).2.2 1 := by
  have hlen : (State.get s WCUR).length = l.length := by rw [hC]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct scanBody WIDX l.length s
    (fun i st => State.get st WCUR = l.drop i
      ∧ State.get st WSA = flagOf (scanTake l i).1
      ∧ State.get st WSB = flagOf (scanTake l i).2.1
      ∧ State.get st WTAL = List.replicate (scanTake l i).2.2 1)
    ⟨by simpa using hC, by rw [hA, scanTake_zero]; rfl,
      by rw [hB, scanTake_zero]; rfl, by rw [hT, scanTake_zero]; rfl⟩
    (by
      rintro i st hi ⟨h1, h2, h3, h4⟩
      refine scanBody_run l i hi _ ?_ ?_ ?_ ?_
      · rw [State.get_set_ne _ WIDX _ WCUR (by decide)]; exact h1
      · rw [State.get_set_ne _ WIDX _ WSA (by decide)]; exact h2
      · rw [State.get_set_ne _ WIDX _ WSB (by decide)]; exact h3
      · rw [State.get_set_ne _ WIDX _ WTAL (by decide)]; exact h4)
  simp only [scanTake_length] at key
  exact ⟨key.2.1, key.2.2.1, key.2.2.2⟩

/-! ## The builder meets `EvalCnfSplit.satEIn` -/

/-- The state the loop starts from. -/
theorem satStrPre_eval (x c : List Bool) :
    State.get (satStrPre.eval (strEIn (x, c))) WCUR = strBits x
      ∧ State.get (satStrPre.eval (strEIn (x, c))) WSA = []
      ∧ State.get (satStrPre.eval (strEIn (x, c))) WSB = []
      ∧ State.get (satStrPre.eval (strEIn (x, c))) WTAL = []
      ∧ State.get (satStrPre.eval (strEIn (x, c))) 0 = strBits x
      ∧ State.get (satStrPre.eval (strEIn (x, c))) ASSGN = strBits c := by
  have hg0 : State.get (strEIn (x, c)) 0 = strBits x := rfl
  have hg1 : State.get (strEIn (x, c)) 1 = strBits c := rfl
  have e1 : (Cmd.op (Op.copy ASSGN 1)).eval (strEIn (x, c))
      = (strEIn (x, c)).set ASSGN (strBits c) := by
    rw [Cmd.eval_op]
    show (strEIn (x, c)).set ASSGN (State.get (strEIn (x, c)) 1) = _
    rw [hg1]
  have hg0' : State.get ((strEIn (x, c)).set ASSGN (strBits c)) 0 = strBits x := by
    rw [State.get_set_ne _ ASSGN _ 0 (by decide)]; exact hg0
  have e2 : (Cmd.op (Op.copy WCUR 0)).eval ((strEIn (x, c)).set ASSGN (strBits c))
      = ((strEIn (x, c)).set ASSGN (strBits c)).set WCUR (strBits x) := by
    rw [Cmd.eval_op]
    show ((strEIn (x, c)).set ASSGN (strBits c)).set WCUR
        (State.get ((strEIn (x, c)).set ASSGN (strBits c)) 0) = _
    rw [hg0']
  rw [satStrPre, Cmd.eval_seq, e1, Cmd.eval_seq, e2]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.get_set_ne _ WTAL _ WCUR (by decide),
      State.get_set_ne _ WSB _ WCUR (by decide),
      State.get_set_ne _ WSA _ WCUR (by decide), State.get_set_eq]
  · rw [State.get_set_ne _ WTAL _ WSA (by decide),
      State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
  · rw [State.get_set_ne _ WTAL _ WSB (by decide), State.get_set_eq]
  · rw [State.get_set_eq]
  · rw [State.get_set_ne _ WTAL _ 0 (by decide),
      State.get_set_ne _ WSB _ 0 (by decide),
      State.get_set_ne _ WSA _ 0 (by decide),
      State.get_set_ne _ WCUR _ 0 (by decide)]
    exact hg0'
  · rw [State.get_set_ne _ WTAL _ ASSGN (by decide),
      State.get_set_ne _ WSB _ ASSGN (by decide),
      State.get_set_ne _ WSA _ ASSGN (by decide),
      State.get_set_ne _ WCUR _ ASSGN (by decide), State.get_set_eq]

set_option maxHeartbeats 1000000 in
/-- The four registers the builder must produce. -/
theorem satStrBuild_get (x c : List Bool) :
    State.get (satStrBuild.eval (strEIn (x, c))) OUTPUT = []
      ∧ State.get (satStrBuild.eval (strEIn (x, c))) CLAUSE_TALLY
          = List.replicate (cnfOf x).length 1
      ∧ State.get (satStrBuild.eval (strEIn (x, c))) CNF_STREAM = encodeCnf (cnfOf x)
      ∧ State.get (satStrBuild.eval (strEIn (x, c))) ASSGN = strBits c := by
  obtain ⟨hC0, hA0, hB0, hT0, hI0, hAS0⟩ := satStrPre_eval x c
  set s0 : State := satStrPre.eval (strEIn (x, c)) with hs0
  set u : State := (Cmd.forBnd WIDX WCUR scanBody).eval s0 with hu
  obtain ⟨hUA, hUB, hUT⟩ := scanLoop_run (strBits x) s0 hC0 hA0 hB0 hT0
  -- the loop touches nothing below `19`
  have hframe : ∀ q : Var, q ∉ (Cmd.forBnd WIDX WCUR scanBody).writes →
      State.get u q = State.get s0 q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  have hU0 : State.get u 0 = strBits x := by
    rw [hu, hframe 0 (by decide)]; exact hI0
  have hUAS : State.get u ASSGN = strBits c := by
    rw [hu, hframe ASSGN (by decide)]; exact hAS0
  -- lay the layout
  have hUT' : State.get u WTAL = List.replicate (scanRun (strBits x)).2.2 1 := hUT
  set cnt : Nat := (scanRun (strBits x)).2.2 with hcnt
  have hpostA : satStrPostA.eval u
      = (((u.set CNF_STREAM (strBits x)).set CLAUSE_TALLY (List.replicate cnt 1)).set OUTPUT
          []).set WHD (if (scanRun (strBits x)).1 then [1] else [0]) := by
    rw [satStrPostA, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    simp only [Cmd.eval_op, Op.eval, hU0]
    have h1 : State.get (u.set CNF_STREAM (strBits x)) WTAL = List.replicate cnt 1 := by
      rw [State.get_set_ne _ CNF_STREAM _ WTAL (by decide)]; exact hUT'
    rw [h1]
    have h2 : State.get (((u.set CNF_STREAM (strBits x)).set CLAUSE_TALLY
        (List.replicate cnt 1)).set OUTPUT []) WSA = flagOf (scanRun (strBits x)).1 := by
      rw [State.get_set_ne _ OUTPUT _ WSA (by decide),
        State.get_set_ne _ CLAUSE_TALLY _ WSA (by decide),
        State.get_set_ne _ CNF_STREAM _ WSA (by decide)]
      exact hUA
    rw [h2]
    cases (scanRun (strBits x)).1 <;> rfl
  set w : State := (((u.set CNF_STREAM (strBits x)).set CLAUSE_TALLY
    (List.replicate cnt 1)).set OUTPUT []) with hw
  -- the four registers of `w`, before the malformed fix-up
  have hw0 : State.get w OUTPUT = [] := State.get_set_eq _ _ _
  have hw1 : State.get w CLAUSE_TALLY = List.replicate cnt 1 := by
    rw [hw, State.get_set_ne _ OUTPUT _ CLAUSE_TALLY (by decide)]
    exact State.get_set_eq _ _ _
  have hw2 : State.get w CNF_STREAM = strBits x := by
    rw [hw, State.get_set_ne _ OUTPUT _ CNF_STREAM (by decide),
      State.get_set_ne _ CLAUSE_TALLY _ CNF_STREAM (by decide)]
    exact State.get_set_eq _ _ _
  have hw3 : State.get w ASSGN = strBits c := by
    rw [hw, State.get_set_ne _ OUTPUT _ ASSGN (by decide),
      State.get_set_ne _ CLAUSE_TALLY _ ASSGN (by decide),
      State.get_set_ne _ CNF_STREAM _ ASSGN (by decide)]
    exact hUAS
  have hwB : State.get w WSB = flagOf (scanRun (strBits x)).2.1 := by
    rw [hw, State.get_set_ne _ OUTPUT _ WSB (by decide),
      State.get_set_ne _ CLAUSE_TALLY _ WSB (by decide),
      State.get_set_ne _ CNF_STREAM _ WSB (by decide)]
    exact hUB
  -- the malformed fix-up, on any state
  have hbad : ∀ z : State, State.get (badBranch.eval z) OUTPUT = State.get z OUTPUT
      ∧ State.get (badBranch.eval z) CLAUSE_TALLY = [1]
      ∧ State.get (badBranch.eval z) CNF_STREAM = [0]
      ∧ State.get (badBranch.eval z) ASSGN = State.get z ASSGN := by
    intro z
    rw [badBranch, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    simp only [Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
      State.get_set_ne _ CNF_STREAM _ CLAUSE_TALLY (by decide : CLAUSE_TALLY ≠ CNF_STREAM)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ CLAUSE_TALLY _ OUTPUT (by decide),
        State.get_set_ne _ CNF_STREAM _ OUTPUT (by decide)]
    · first | rfl | (rw [State.get_set_eq]; rfl) | simp [flagOf]
    · rw [State.get_set_ne _ CLAUSE_TALLY _ CNF_STREAM (by decide), State.get_set_eq]; rfl
    · rw [State.get_set_ne _ CLAUSE_TALLY _ ASSGN (by decide),
        State.get_set_ne _ CNF_STREAM _ ASSGN (by decide)]
  -- the malformed cases collapse to the junk CNF
  have hjunk : ∀ z : State, State.get z OUTPUT = [] → State.get z ASSGN = strBits c →
      wfCnfB (strBits x) = false →
      State.get (badBranch.eval z) OUTPUT = []
        ∧ State.get (badBranch.eval z) CLAUSE_TALLY = List.replicate (cnfOf x).length 1
        ∧ State.get (badBranch.eval z) CNF_STREAM = encodeCnf (cnfOf x)
        ∧ State.get (badBranch.eval z) ASSGN = strBits c := by
    intro z hz0 hz3 hnw
    obtain ⟨b0, b1, b2, b3⟩ := hbad z
    have hb : cnfOf x = botCnf := parseTotal_of_not_wf _ hnw
    exact ⟨by rw [b0, hz0], by rw [b1, hb]; rfl, by rw [b2, hb]; rfl, by rw [b3, hz3]⟩
  rw [satStrBuild, Cmd.eval_seq, ← hs0, Cmd.eval_seq, ← hu, Cmd.eval_seq, hpostA]
  clear_value w
  clear hpostA hw hu hs0 hUA hUB hUT hUT' hframe
  cases ha : (scanRun (strBits x)).1 with
  | true =>
      have hflag : State.get (w.set WHD [1]) WHD = [1] := State.get_set_eq _ _ _
      rw [if_pos rfl, satStrPostB, Cmd.eval_ifBit_true _ _ _ _ hflag]
      have hnw : wfCnfB (strBits x) = false := by
        show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = false
        rw [ha]; rfl
      refine hjunk _ ?_ ?_ hnw
      · rw [State.get_set_ne _ WHD _ OUTPUT (by decide)]; exact hw0
      · rw [State.get_set_ne _ WHD _ ASSGN (by decide)]; exact hw3
  | false =>
      have hflag : State.get (w.set WHD [0]) WHD ≠ [1] := by
        rw [State.get_set_eq]; simp
      rw [if_neg (by simp), satStrPostB, Cmd.eval_ifBit_false _ _ _ _ hflag,
        Cmd.eval_seq]
      have hWSB : State.get (w.set WHD [0]) WSB = flagOf (scanRun (strBits x)).2.1 := by
        rw [State.get_set_ne _ WHD _ WSB (by decide)]; exact hwB
      have hstep : (Cmd.op (Op.nonEmpty WHD WSB)).eval (w.set WHD [0])
          = w.set WHD (if (scanRun (strBits x)).2.1 then [1] else [0]) := by
        rw [Cmd.eval_op]
        show (w.set WHD [0]).set WHD
            (if (State.get (w.set WHD [0]) WSB).isEmpty then [0] else [1]) = _
        rw [hWSB, State.set_set]
        cases (scanRun (strBits x)).2.1 <;> rfl
      rw [hstep]
      cases hb : (scanRun (strBits x)).2.1 with
      | true =>
          have hflag2 : State.get (w.set WHD [1]) WHD = [1] := State.get_set_eq _ _ _
          rw [if_pos rfl, Cmd.eval_ifBit_true _ _ _ _ hflag2]
          have hnw : wfCnfB (strBits x) = false := by
            show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = false
            rw [ha, hb]; rfl
          refine hjunk _ ?_ ?_ hnw
          · rw [State.get_set_ne _ WHD _ OUTPUT (by decide)]; exact hw0
          · rw [State.get_set_ne _ WHD _ ASSGN (by decide)]; exact hw3
      | false =>
          have hflag2 : State.get (w.set WHD [0]) WHD ≠ [1] := by
            rw [State.get_set_eq]; simp
          rw [if_neg (by simp), Cmd.eval_ifBit_false _ _ _ _ hflag2]
          have hwf : wfCnfB (strBits x) = true := by
            show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = true
            rw [ha, hb]; rfl
          have hstream : encodeCnf (cnfOf x) = strBits x :=
            encodeCnf_parseTotal _ (strBits_bit x) hwf
          have hlen : cnt = (cnfOf x).length := by
            rw [hcnt]
            show cnfCount (strBits x) = _
            exact cnfCount_eq_length _ (strBits_bit x) hwf
          have hclr : (Cmd.op (Op.clear WHD)).eval (w.set WHD [0]) = w.set WHD [] := by
            rw [Cmd.eval_op]
            show (w.set WHD [0]).set WHD [] = _
            rw [State.set_set]
          rw [hclr]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [State.get_set_ne _ WHD _ OUTPUT (by decide)]; exact hw0
          · rw [State.get_set_ne _ WHD _ CLAUSE_TALLY (by decide), hw1, hlen]
          · rw [State.get_set_ne _ WHD _ CNF_STREAM (by decide), hw2, hstream]
          · rw [State.get_set_ne _ WHD _ ASSGN (by decide)]; exact hw3

/-! ## The bridge

`satStrBuild` writes only registers `0`–`3` and `19`–`24`, so registers `4`–`18`
are untouched and already `[]` on both sides. What is left is the four values
above — and then `EvalCnfSplit.certDecode`'s already-proven bridge, pushed
through by `Cmd.eval_agree`. -/

/-- **The builder hands the certificate decoder exactly its own input layout.**
`19` is `certDecode`'s frame, so this is enough to reuse its bridge verbatim. -/
theorem satStrBuild_bridge (x c : List Bool) :
    AgreeBelow 19 (satStrBuild.eval (strEIn (x, c))) (EvalCnfSplit.satEIn (cnfOf x, c)) := by
  obtain ⟨h0, h1, h2, h3⟩ := satStrBuild_get x c
  have hframe : ∀ q : Var, q ∉ satStrBuild.writes →
      State.get (satStrBuild.eval (strEIn (x, c))) q = State.get (strEIn (x, c)) q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  intro r hr
  interval_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rw [hframe 4 (by decide)]; rfl
  · rw [hframe 5 (by decide)]; rfl
  · rw [hframe 6 (by decide)]; rfl
  · rw [hframe 7 (by decide)]; rfl
  · rw [hframe 8 (by decide)]; rfl
  · rw [hframe 9 (by decide)]; rfl
  · rw [hframe 10 (by decide)]; rfl
  · rw [hframe 11 (by decide)]; rfl
  · rw [hframe 12 (by decide)]; rfl
  · rw [hframe 13 (by decide)]; rfl
  · rw [hframe 14 (by decide)]; rfl
  · rw [hframe 15 (by decide)]; rfl
  · rw [hframe 16 (by decide)]; rfl
  · rw [hframe 17 (by decide)]; rfl
  · rw [hframe 18 (by decide)]; rfl

/-- The pair map the re-encoder implements: parse the input string, decode the
certificate bits. -/
def gStr (v : List Bool × List Bool) : cnf × assgn :=
  (cnfOf v.1, EvalCnfSplit.decodeBits v.2)

/-- **The full re-encoding law.** After `satStrMfc` the state agrees with the
live SAT verifier's own input layout on the verifier's whole frame. -/
theorem satStrMfc_bridge (v : List Bool × List Bool) :
    AgreeBelow 16 (satStrMfc.eval (strEIn v)) (encodeState (gStr v)) := by
  rcases v with ⟨x, c⟩
  have h1 : AgreeBelow 19 (EvalCnfSplit.certDecode.eval (satStrBuild.eval (strEIn (x, c))))
      (EvalCnfSplit.certDecode.eval (EvalCnfSplit.satEIn (cnfOf x, c))) :=
    Cmd.eval_agree _ 19 EvalCnfSplit.certDecode_usesBelow (satStrBuild_bridge x c)
  have h2 := EvalCnfSplit.certDecode_bridge (cnfOf x, c)
  intro r hr
  rw [satStrMfc, Cmd.eval_seq]
  exact (h1 r (by omega)).trans (h2 r hr)

/-! ## Sizes and the cost budget -/

theorem size_botCnf : encodable.size botCnf = 1 := rfl

/-- The parsed CNF is never bigger than the string it came from. On the
well-formed branch this is the *no-compression* half of the `Serialize cnf`
sandwich (`CnfSerialize.size_le_encodeCnf_length`); on the junk branch the CNF
is the constant `[[]]`. -/
theorem size_cnfOf_le (x : List Bool) : encodable.size (cnfOf x) ≤ encodable.size x + 1 := by
  by_cases hwf : wfCnfB (strBits x) = true
  · have h1 := CnfSerialize.size_le_encodeCnf_length (cnfOf x)
    have h2 : encodeCnf (cnfOf x) = strBits x :=
      encodeCnf_parseTotal _ (strBits_bit x) hwf
    have h3 : x.length ≤ encodable.size x := Complexity.Lang.length_le_size x
    rw [h2, strBits_length] at h1
    omega
  · have : cnfOf x = botCnf := parseTotal_of_not_wf _ (by simpa using hwf)
    rw [this, size_botCnf]
    omega

/-- The argument the SAT verifier's own quartic budget is applied at. -/
def gArg (n : Nat) : Nat := n * n + n + 2

theorem gArg_poly : inOPoly gArg :=
  inOPoly_add (inOPoly_add (inOPoly_mul inOPoly_id inOPoly_id) inOPoly_id) (inOPoly_const 2)

theorem gArg_mono : monotonic gArg := by
  intro a b h
  show a * a + a + 2 ≤ b * b + b + 2
  have := Nat.mul_le_mul h h
  omega

theorem le_gArg (n : Nat) : n ≤ gArg n := by show n ≤ n * n + n + 2; omega

theorem size_gStr_le (v : List Bool × List Bool) :
    encodable.size (gStr v) ≤ gArg (encodable.size v) := by
  rcases v with ⟨x, c⟩
  have hx := size_cnfOf_le x
  have hc := EvalCnfSplit.size_decodeBits_le c
  have hn : encodable.size ((x, c) : List Bool × List Bool)
      = encodable.size x + encodable.size c + 1 := rfl
  show encodable.size (cnfOf x) + encodable.size (EvalCnfSplit.decodeBits c) + 1
      ≤ gArg (encodable.size ((x, c) : List Bool × List Bool))
  rw [hn]
  show _ ≤ (encodable.size x + encodable.size c + 1) * (encodable.size x + encodable.size c + 1)
    + (encodable.size x + encodable.size c + 1) + 2
  nlinarith [Nat.zero_le (encodable.size x), Nat.zero_le (encodable.size c)]

theorem strEIn_size_le (v : List Bool × List Bool) :
    State.size (strEIn v) ≤ encodable.size v := by
  rcases v with ⟨x, c⟩
  have hx : x.length ≤ encodable.size x := Complexity.Lang.length_le_size x
  have hc : c.length ≤ encodable.size c := Complexity.Lang.length_le_size c
  have hn : encodable.size ((x, c) : List Bool × List Bool)
      = encodable.size x + encodable.size c + 1 := rfl
  rw [strEIn_size, hn]
  omega

theorem le_timeBound (n : Nat) : n ≤ EvalCnfTM.timeBound n := by
  show n ≤ 200000 * (n + 1) ^ 4
  have h : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega

/-! ### The cost of the re-encoder — one decidable pass

`Cmd.chk` (`Lang/CostGrow.lean`) turns the scan into a polynomial, so the whole
cost obligation is `by decide` plus the two size facts above. -/

/-- The `Cmd.chk` seed mask: every register `< 25` is bounded by the input at
entry. -/
def strRegs : Nat := 2 ^ 25 - 1

theorem satStrMfc_chk : (satStrMfc.chk strRegs).1 = true := by decide

theorem satStrMfc_usesBelow : Cmd.UsesBelow satStrMfc 25 := by
  simp [satStrMfc, satStrBuild, satStrPre, satStrPostA, satStrPostB, badBranch, scanBody,
    EvalCnfSplit.certDecode, EvalCnfSplit.decodeBody, Cmd.UsesBelow, Op.UsesBelow,
    WCUR, WIDX, WHD, WSA, WSB, WTAL, EvalCnfSplit.DCUR, EvalCnfSplit.DIDX,
    EvalCnfSplit.DHD, OUTPUT, CLAUSE_TALLY, CNF_STREAM, ASSGN]

/-- The re-encoder's cost, as an existential polynomial (FINDING Y). -/
theorem satStrMfc_cost : ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ v : List Bool × List Bool, satStrMfc.cost (strEIn v) ≤ budget (encodable.size v) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk satStrMfc strRegs satStrMfc_chk
  refine ⟨fun n => K * (n + 1) ^ (D + 1), ?_, ?_, fun v => hb (strEIn v) _ (strEIn_size_le v)⟩
  · refine inOPoly_mul (inOPoly_const K) ⟨D + 1, 2 ^ (D + 1), 1, ?_⟩
    intro n hn
    calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
  · exact fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- The composite verifier's budget: the re-encoder's, plus the SAT verifier's
quartic at the parsed instance's size. -/
noncomputable def strBound : Nat → Nat :=
  fun n => satStrMfc_cost.choose n + EvalCnfTM.timeBound (gArg n) + 1

theorem strBound_poly : inOPoly strBound :=
  inOPoly_add (inOPoly_add satStrMfc_cost.choose_spec.1
    (inOPoly_comp (f := gArg) (g := EvalCnfTM.timeBound) gArg_poly EvalCnfTM.timeBound_inOPoly)) (inOPoly_const 1)

theorem strBound_mono : monotonic strBound := by
  intro a b hab
  have h1 := satStrMfc_cost.choose_spec.2.1 a b hab
  have h2 := EvalCnfTM.timeBound_monotonic _ _ (gArg_mono a b hab)
  show _ + _ + 1 ≤ _ + _ + 1
  omega

theorem le_strBound (n : Nat) : n ≤ strBound n := by
  have h1 : n ≤ EvalCnfTM.timeBound (gArg n) :=
    le_trans (le_gArg n) (le_trans (le_timeBound (gArg n))
      (EvalCnfTM.timeBound_monotonic _ _ (Nat.le_refl _)))
  show n ≤ _ + _ + 1
  omega

/-! ## The composite verifier and the witness -/

/-- **The `FreePrecomposeData`.** `eIn` is the *canonical string layout* — all
the work is in `mfc`, which is the honesty discipline of standing risk #1. -/
noncomputable def strPrecomposeData :
    EvalCnfTM.evalCnfDecidesLang.FreePrecomposeData gStr where
  mfc := satStrMfc
  eIn := strEIn
  newBound := strBound
  newBound_poly := strBound_poly
  newBound_mono := strBound_mono
  bridge := satStrMfc_bridge
  encodeIn_size := fun v => le_trans (strEIn_size_le v) (le_strBound _)
  cost_bound := fun v => by
    have h1 : satStrMfc.cost (strEIn v) ≤ satStrMfc_cost.choose (encodable.size v) :=
      satStrMfc_cost.choose_spec.2.2 v
    have h2 : evalCnfCmd.cost (satStrMfc.eval (strEIn v))
        = evalCnfCmd.cost (encodeState (gStr v)) :=
      Cmd.cost_agree _ 16 evalCnfCmd_usesBelow (satStrMfc_bridge v)
    have h3 : evalCnfCmd.cost (encodeState (gStr v))
        ≤ EvalCnfTM.timeBound (gArg (encodable.size v)) :=
      le_trans (evalCnfCmd_cost_bound _)
        (EvalCnfTM.timeBound_monotonic _ _ (size_gStr_le v))
    show (satStrMfc ;; evalCnfCmd).cost (strEIn v) ≤ strBound (encodable.size v)
    rw [Cmd.cost_seq, h2]
    show 1 + satStrMfc.cost (strEIn v) + _
        ≤ satStrMfc_cost.choose _ + EvalCnfTM.timeBound (gArg _) + 1
    omega
  enc_bit := strEIn_bit
  regBound := 25
  usesBelow := ⟨satStrMfc_usesBelow, Cmd.UsesBelow_mono (by omega) evalCnfCmd_usesBelow⟩
  width_le := fun v => by
    rcases v with ⟨x, c⟩
    show (strEIn (x, c)).length ≤ 25
    rw [strEIn_lit]
    simp

/-- **The certificate relation**: the bit string, read as a characteristic
vector, satisfies the CNF the input string spells out. -/
def satStrRel (x c : List Bool) : Prop :=
  satisfiesCnf (EvalCnfSplit.decodeBits c) (cnfOf x)

/-- **The verifier for `SATStr`** — a real `Cmd` on the canonical string
layout. -/
noncomputable def satStrVerifier :
    DecidesLang (fun v : List Bool × List Bool => satStrRel v.1 v.2) strBound :=
  EvalCnfTM.evalCnfDecidesLang.precomposeFree gStr strPrecomposeData

/-- **The certificate relation is sound, complete and polynomially bounded.**
Reuses `EvalCnfSplit.satRel_correct` at the parsed CNF; the only new content is
that the parse never inflates the instance (`size_cnfOf_le`). -/
theorem satStrRel_correct : polyCertRel SATStr satStrRel := by
  obtain ⟨R⟩ := EvalCnfSplit.satRel_correct
  refine ⟨⟨fun n => R.bound (n + 1), ?_, ?_, ?_, ?_⟩⟩
  · rintro x c h
    exact ⟨EvalCnfSplit.decodeBits c, h⟩
  · intro x hx
    obtain ⟨c, hrel, hsize⟩ := R.complete hx
    exact ⟨c, hrel, le_trans hsize (R.bound_mono _ _ (size_cnfOf_le x))⟩
  · exact inOPoly_comp (f := fun n => n + 1) (g := R.bound)
      (inOPoly_add inOPoly_id (inOPoly_const 1)) R.bound_poly
  · exact fun a b hab => R.bound_mono _ _ (by omega)

/-- **The witness: `SATStr` is an NP string language.** Every field discharged,
`sorry`-free, over the canonical one-register layout — no `encX` to choose. -/
noncomputable def satStrWitness : Complexity.Lang.InNPWitnessStr SATStr where
  rel := satStrRel
  dBound := strBound
  dBound_poly := strBound_poly
  dBound_mono := strBound_mono
  verifier := satStrVerifier
  rel_correct := satStrRel_correct
  encX := certState
  encodeIn_eq := fun _ _ => rfl
  xWidth := 1
  encX_width := fun _ => rfl
  encX_size := fun x => by
    have h : State.size (certState x) = x.length := Complexity.Lang.State.size_certState x
    have h2 : x.length ≤ encodable.size x := Complexity.Lang.length_le_size x
    have h3 := le_strBound (encodable.size x)
    omega
  sizeLB := fun n => 2 * n
  sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
  encX_sizeLB := fun x => by
    rw [Complexity.Lang.State.size_certState]
    exact Complexity.Lang.size_le_two_mul_length x
  encX_canonical := fun _ => rfl

/-- **`SATStr` is in the hypothesis class of `CookLevinHonest.CookLevinStr`.** -/
theorem inNPStr_SATStr : Complexity.Lang.inNPStr SATStr := ⟨satStrWitness⟩

/-! ## The certificate is load-bearing

Without this a reader cannot tell that the verifier is not ignoring its
certificate register and deciding something trivial. The composite program is
run, on one input, at two certificates, with two answers. -/

/-- The whole composite verifier program: re-encode, then run the SAT
verifier. -/
def satStrCmd : Cmd := satStrMfc ;; evalCnfCmd

set_option maxRecDepth 100000 in
/-- **The program reads the certificate.** Same input (`encodeCnf [[(true,0)]]`,
i.e. the formula `x₀`), two certificates, two verdicts. -/
theorem verifier_reads_certificate :
    (satStrCmd.eval (strEIn ([true, true, false, false], [true]))).isAccept = true
      ∧ (satStrCmd.eval (strEIn ([true, true, false, false], [false]))).isAccept = false := by
  constructor <;> rfl

set_option maxRecDepth 100000 in
/-- …and it rejects a string that is not an encoding, whatever the certificate:
`[true]` fails the scanner. -/
theorem verifier_rejects_malformed :
    (satStrCmd.eval (strEIn ([true], [true]))).isAccept = false
      ∧ (satStrCmd.eval (strEIn ([true], [false, true]))).isAccept = false := by
  constructor <;> rfl

end SATStr
