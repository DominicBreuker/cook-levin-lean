import Complexity.NP.SAT.CookLevin.Reductions.S1Map
import Complexity.NP.SAT.CookLevin.Reductions.HeadLayout
import Complexity.Complexity.Deciders.CliqueRelTM
import Complexity.Lang.CostFlat

set_option autoImplicit false
set_option maxRecDepth 8000

/-! # S1, part 3 — the program's stages **P (parse)** and **G (guard)**

The first two of the seven stages of `S1Program.s1Program` (`FlatSingleTMGenNP
⪯p' FlatTCC`), built bottom-up as standalone gadgets with `_run` lemmas — the
`FrontProgram` ↔ `FrontWitness` split.

* **P (parse)** drains the frozen head layout's machine register
  `1 = encSyms (flattenTM M)` into the scratch frame: `1^sig`, `1^tapes`,
  `1^states`, `1^start`, `1^|halt|`, the halt **bit list**, `1^|trans|`, and the
  transition sub-stream kept whole (`encSyms (transFlat M)`) for stages G and C
  to re-scan.
* **G (guard)** computes `S1Map.s1GuardB M s` into the single flag register
  `FLG` (`[1]` = true, `[]` = false), from P's outputs plus the input-string
  register `2 = encSyms s`.

## Why these two stages first (the risk order)

Every later stage reads P's outputs and lives inside the register frame P fixes,
and P is the only genuinely *new* gadget kind in the whole program: parsing a
**variable-arity nested** structure (the transition table — each `Option Nat`
occupies one *or two* stream items) out of a flat sentinel stream. Surfacing its
cost before the card emitter is written is what keeps the emitter from being
written twice.

**Finding (2026-07-25-b, measured — `probes/S1ParseProbe.lean` §4): P + G cost
is CUBIC in the input register content, and is therefore NOT the S1 budget
driver.** Growing the transition count, the alphabet and the input string each
give degree ≈ 3, ≈ 1.8 and ≈ 2 respectively. `S1Witness.s1_reductionLang`'s
`cost_bound` is `S1Map.s1Bound n = (2·(n+3))^10`, so P + G leave the whole
degree-10 budget to stage C. Design consequence: **do not spend effort
optimising the parse**; the emitter is the only place where the loop structure
matters.

**Second finding (design, validated by `probes/S1ParseProbe.lean` §1): the parse
never desynchronises, even on invalid machines.** `flattenEntry` writes each
list's *actual* length before its payload, so the item-consuming loops are
driven by the data, not by `M.tapes`. The guard therefore only ever *compares*
those lengths against `tapes`; `stageP_run` and `stageG_run` need **no validity
hypothesis at all**. (That is what lets the multiplex stage discard P's outputs
on the no-branch without any conditional reasoning.)

## The register frame — pinned here, consumed by every later stage

`CliqueRelTM.readNum` / `CliqueRelTM.ltBit` are reused verbatim, so their four
hard-wired scratch registers are **reserved**: `15` (`HEAD`), `16` (`INBLK`),
`22` (`LT_B`), `26` (`SKIPR`). Everything else below `s1RegBound = 48` is free
for stages Σ / I / C / F / M.

| reg | stage P/G role | (input layout) |
|-----|----------------|----------------|
| 0   | `ZERO` — the `andIn` no-op target; must end `[]` (the seam scrub) | `[]` |
| 1   | `MREG` (read-only here) | machine stream |
| 2   | `SREG` (read-only here) | input-string stream |
| 3,4 | untouched by P/G | `1^maxSize`, `1^steps` |
| 5   | untouched by P/G | — |
| 6   | `PSIG` = `1^M.sig` | |
| 7   | `PTAPES` = `1^M.tapes` | |
| 8   | `PSTATES` = `1^M.states` | |
| 9   | `PSTART` = `1^M.start` | |
| 10  | `PNHALT` = `1^M.halt.length` | |
| 11  | `PHALT` = the halt bit list | |
| 12  | `PNTRANS` = `1^M.trans.length` | |
| 13  | `PTRANS` = `encSyms (transFlat M)` | |
| 14  | `SCAN` — the header/input cursor | |
| 17  | `FLG` — the guard flag | |
| 18  | `VAL`, 20 `RES`, 21 `ONE`, 23 `TSCAN`, 24 `NEF` (19, 25 free) | |
| 27–31 | `I1`…`I5` — loop counters | |

Registers `6`–`13` are P's **persistent** outputs; `14`, `17`–`31` are scratch
that later stages may reuse *after* G has run. -/

namespace S1Parse

open Complexity.Lang HeadLayout

/-! ## The register frame -/

def ZERO    : Var := 0
def MREG    : Var := 1
def SREG    : Var := 2
def PSIG    : Var := 6
def PTAPES  : Var := 7
def PSTATES : Var := 8
def PSTART  : Var := 9
def PNHALT  : Var := 10
def PHALT   : Var := 11
def PNTRANS : Var := 12
def PTRANS  : Var := 13
def SCAN    : Var := 14
-- 15 = `CliqueRelTM.HEAD`, 16 = `CliqueRelTM.INBLK` (reserved)
def FLG     : Var := 17
def VAL     : Var := 18
-- 19 free (the arity register turned out unnecessary: `forBnd` samples its
-- bound's length once at entry, so `VAL` can double as bound and scratch)
def RES     : Var := 20
def ONE     : Var := 21
-- 22 = `CliqueRelTM.LT_B` (reserved)
def TSCAN   : Var := 23
def NEF     : Var := 24
-- 26 = `CliqueRelTM.SKIPR` (reserved)
def I1      : Var := 27
def I2      : Var := 28
def I3      : Var := 29
def I4      : Var := 30
def I5      : Var := 31

/-! ## The pure stream model

`flattenTM`/`flattenEntry` accumulate with `foldl (fun a e => a ++ f e)`; every
inductive argument wants `flatMap`. These two abbreviations + `optsFlat_eq`
/`transFlat_eq` are the bridge (the same move `HeadLayout.foldl_append_acc`
makes for `encSyms_append`). -/

/-- The flattened option list of an entry field. -/
def optsFlat (l : List (Option Nat)) : List Nat := l.flatMap encOptN

/-- The flattened transition table. -/
def transFlat (M : FlatTM) : List Nat := M.trans.flatMap flattenEntry

private theorem foldl_append_nil {α : Type} (g : α → List Nat) (m : List α) :
    ∀ acc : List Nat,
      m.foldl (fun a v => a ++ g v) acc = acc ++ m.flatMap g := by
  induction m with
  | nil => intro acc; simp
  | cons v vs ih =>
      intro acc
      rw [List.foldl_cons, ih (acc ++ g v), List.flatMap_cons, List.append_assoc]

theorem optsFlat_eq (l : List (Option Nat)) :
    l.foldl (fun a o => a ++ encOptN o) [] = optsFlat l := by
  rw [foldl_append_nil]; simp [optsFlat]

theorem transFlat_eq (M : FlatTM) :
    M.trans.foldl (fun a e => a ++ flattenEntry e) [] = transFlat M := by
  rw [foldl_append_nil]; simp [transFlat]

/-- One entry's stream, in `flatMap` form. -/
theorem flattenEntry_eq (e : FlatTMTransEntry) :
    flattenEntry e
      = [e.src_state, e.src_tape_vals.length] ++ optsFlat e.src_tape_vals
        ++ [e.dst_state, e.dst_write_vals.length] ++ optsFlat e.dst_write_vals
        ++ [e.move_dirs.length] ++ e.move_dirs.map encMoveN := by
  unfold flattenEntry
  rw [optsFlat_eq, optsFlat_eq]

/-- The header decomposition of `flattenTM`. -/
theorem flattenTM_eq (M : FlatTM) :
    flattenTM M
      = [M.sig, M.tapes, M.states, M.start, M.halt.length]
        ++ M.halt.map (fun b => if b then 1 else 0)
        ++ [M.trans.length] ++ transFlat M := by
  unfold flattenTM
  rw [transFlat_eq]

/-! ## `encSyms` as a cons-list of items -/

/-- The sentinel item of one value: `1 1^v 0`. -/
def itemOf (v : Nat) : List Nat := 1 :: (List.replicate v 1 ++ [0])

theorem encSyms_nil : encSyms [] = [] := rfl

theorem encSyms_cons (v : Nat) (l : List Nat) :
    encSyms (v :: l) = itemOf v ++ encSyms l := by
  show encSyms ([v] ++ l) = _
  rw [encSyms_append]
  rfl

/-- The shape `readItem` consumes: one item followed by the rest of the stream. -/
theorem encSyms_cons' (v : Nat) (l : List Nat) :
    encSyms (v :: l) = 1 :: (List.replicate v 1 ++ 0 :: encSyms l) := by
  rw [encSyms_cons, itemOf]
  simp

end S1Parse

namespace S1Parse

open Complexity.Lang HeadLayout

/-! ## The item reader

`CliqueRelTM.readNum` consumes a *bare* terminated unary block `1^v 0`; an
`encSyms` item carries a leading `1` marker (that marker is what makes
"is there another item?" a `nonEmpty` test). So `readItem` is one `tail` plus
`readNum`. `RegOK` bundles `readNum_run`'s twelve disjointness side conditions
so use sites discharge them with a single `by decide`. -/

/-- `readNum`'s scratch-disjointness side conditions, bundled. -/
abbrev RegOK (dst stream idx : Var) : Prop :=
  stream ≠ dst ∧ stream ≠ idx ∧ dst ≠ idx ∧
  stream ≠ CliqueRelTM.HEAD ∧ stream ≠ CliqueRelTM.INBLK ∧ stream ≠ CliqueRelTM.SKIPR ∧
  dst ≠ CliqueRelTM.HEAD ∧ dst ≠ CliqueRelTM.INBLK ∧ dst ≠ CliqueRelTM.SKIPR ∧
  idx ≠ CliqueRelTM.HEAD ∧ idx ≠ CliqueRelTM.INBLK ∧ idx ≠ CliqueRelTM.SKIPR

/-- Drain one `encSyms` item `1 1^v 0` off `stream` into `dst` (as `1^v`). -/
def readItem (dst stream idx : Var) : Cmd :=
  Cmd.op (.tail stream stream) ;; CliqueRelTM.readNum dst stream idx

/-- **The item reader is correct.** -/
theorem readItem_run (st : State) (v : Nat) (rest : List Nat)
    (dst stream idx : Var) (hok : RegOK dst stream idx)
    (hstream : st.get stream = encSyms (v :: rest)) :
    ((readItem dst stream idx).eval st).get dst = List.replicate v 1
    ∧ ((readItem dst stream idx).eval st).get stream = encSyms rest := by
  obtain ⟨hsd, hsi, hdi, hsH, hsI, hsS, hdH, hdI, hdS, hiH, hiI, hiS⟩ := hok
  have e1 : (readItem dst stream idx).eval st
      = (CliqueRelTM.readNum dst stream idx).eval
          (st.set stream (List.replicate v 1 ++ 0 :: encSyms rest)) := by
    unfold readItem
    rw [Cmd.eval_seq, Cmd.eval_op]
    simp only [Op.eval, hstream, encSyms_cons', List.tail_cons]
  have hget : (st.set stream (List.replicate v 1 ++ 0 :: encSyms rest)).get stream
      = List.replicate v 1 ++ 0 :: encSyms rest := State.get_set_eq _ _ _
  have h := CliqueRelTM.readNum_run
    (st.set stream (List.replicate v 1 ++ 0 :: encSyms rest)) v (encSyms rest)
    dst stream idx hget hsd hsi hdi hsH hsI hsS hdH hdI hdS hiH hiI hiS
  rw [e1]
  exact ⟨h.1, h.2.1⟩


/-! ## Stage P — the parse

Ten steps: copy the machine register into the cursor `SCAN`, drain the five
header items, drain the `|halt|` halt items into the bit list `PHALT`, drain
`|trans|`, and hand the rest of the cursor to `PTRANS`. -/

/-- The numeric code of a halt bit (matching `HeadLayout.flattenTM`). -/
def bitOf (b : Bool) : Nat := if b then 1 else 0

/-- One halt-bit iteration: read the item, append its bit to `PHALT`. -/
def haltBody : Cmd :=
  readItem VAL SCAN I1 ;;
  Cmd.op (.nonEmpty NEF VAL) ;;
  Cmd.ifBit NEF (Cmd.op (.appendOne PHALT)) (Cmd.op (.appendZero PHALT))

/-! Stage P is built as a chain of **named suffixes**. That is not cosmetic:
each parsed register's final value then follows from ONE
`Cmd.eval_get_of_not_writes` applied to the whole remaining suffix (`by decide`
on its write set), instead of a preservation step per later command. Copy this
shape for the remaining stages. -/

def pSuf9 : Cmd := Cmd.op (.copy PTRANS SCAN)
def pSuf8 : Cmd := readItem PNTRANS SCAN I1 ;; pSuf9
def pSuf7 : Cmd := Cmd.forBnd I2 PNHALT haltBody ;; pSuf8
def pSuf6 : Cmd := Cmd.op (.clear PHALT) ;; pSuf7
def pSuf5 : Cmd := readItem PNHALT SCAN I1 ;; pSuf6
def pSuf4 : Cmd := readItem PSTART SCAN I1 ;; pSuf5
def pSuf3 : Cmd := readItem PSTATES SCAN I1 ;; pSuf4
def pSuf2 : Cmd := readItem PTAPES SCAN I1 ;; pSuf3
def pSuf1 : Cmd := readItem PSIG SCAN I1 ;; pSuf2

/-- **Stage P.** -/
def stageP : Cmd := Cmd.op (.copy SCAN MREG) ;; pSuf1

/-! ### List helpers for the halt loop -/

private theorem drop_map_cons {α β : Type} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) :
    (l.drop i).map f = f (l[i]'h) :: (l.drop (i + 1)).map f := by
  rw [List.drop_eq_getElem_cons h, List.map_cons]

private theorem take_map_snoc {α β : Type} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) :
    (l.take (i + 1)).map f = (l.take i).map f ++ [f (l[i]'h)] := by
  rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem h]
  rfl

/-! ### The halt-bit loop -/

private theorem haltBody_step (bs : List Bool) (rest : List Nat) (i : Nat)
    (hi : i < bs.length) (s : State)
    (hSCAN : s.get SCAN = encSyms ((bs.drop i).map bitOf ++ rest))
    (hPH : s.get PHALT = (bs.take i).map bitOf) :
    (haltBody.eval (s.set I2 (List.replicate i 1))).get SCAN
        = encSyms ((bs.drop (i + 1)).map bitOf ++ rest)
    ∧ (haltBody.eval (s.set I2 (List.replicate i 1))).get PHALT
        = (bs.take (i + 1)).map bitOf := by
  set s0 := s.set I2 (List.replicate i 1) with hs0
  have hS0 : s0.get SCAN = encSyms (bitOf (bs[i]'hi) :: ((bs.drop (i+1)).map bitOf ++ rest)) := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (SCAN : Var) ≠ I2), hSCAN,
      drop_map_cons bitOf bs i hi]
    rfl
  have hP0 : s0.get PHALT = (bs.take i).map bitOf := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (PHALT : Var) ≠ I2)]; exact hPH
  obtain ⟨hval, hscan⟩ := readItem_run s0 (bitOf (bs[i]'hi))
    ((bs.drop (i+1)).map bitOf ++ rest) VAL SCAN I1 (by decide) hS0
  set s1 := (readItem VAL SCAN I1).eval s0 with hs1
  have hP1 : s1.get PHALT = (bs.take i).map bitOf := by
    rw [hs1, Cmd.eval_get_of_not_writes _ _ _ (by decide : (PHALT : Var) ∉ (readItem VAL SCAN I1).writes)]
    exact hP0
  have heval : haltBody.eval s0
      = (Cmd.ifBit NEF (Cmd.op (.appendOne PHALT)) (Cmd.op (.appendZero PHALT))).eval
          (s1.set NEF (if (List.replicate (bitOf (bs[i]'hi)) 1 : List Nat).isEmpty then [0] else [1])) := by
    unfold haltBody
    rw [Cmd.eval_seq, Cmd.eval_seq, ← hs1, Cmd.eval_op]
    simp only [Op.eval, hval]
  set s2 := s1.set NEF (if (List.replicate (bitOf (bs[i]'hi)) 1 : List Nat).isEmpty then [0] else [1]) with hs2
  have hP2 : s2.get PHALT = (bs.take i).map bitOf := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (PHALT : Var) ≠ NEF)]; exact hP1
  have hS2 : s2.get SCAN = encSyms ((bs.drop (i+1)).map bitOf ++ rest) := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (SCAN : Var) ≠ NEF)]; exact hscan
  rw [heval]
  have hsnoc := take_map_snoc bitOf bs i hi
  by_cases hb : (bs[i]'hi) = true
  · have hne : s2.get NEF = [1] := by
      rw [hs2, State.get_set_eq]
      simp [bitOf, hb]
    rw [Cmd.eval_ifBit_true _ _ _ _ hne, Cmd.eval_op]
    refine ⟨?_, ?_⟩
    · simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (SCAN : Var) ≠ PHALT)]
      exact hS2
    · simp only [Op.eval, State.get_set_eq, hP2]
      rw [hsnoc]
      simp [bitOf, hb]
  · have hbf : (bs[i]'hi) = false := by simpa using hb
    have hne : s2.get NEF ≠ [1] := by
      rw [hs2, State.get_set_eq]
      simp [bitOf, hbf]
    rw [Cmd.eval_ifBit_false _ _ _ _ hne, Cmd.eval_op]
    refine ⟨?_, ?_⟩
    · simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (SCAN : Var) ≠ PHALT)]
      exact hS2
    · simp only [Op.eval, State.get_set_eq, hP2]
      rw [hsnoc]
      simp [bitOf, hbf]

/-- **The halt-bit loop is correct**: it drains `|bs|` items off `SCAN` and
materialises the bit list on `PHALT`. -/
theorem haltLoop_run (bs : List Bool) (rest : List Nat) (s : State)
    (hSCAN : s.get SCAN = encSyms (bs.map bitOf ++ rest))
    (hPH : s.get PHALT = [])
    (hbnd : (s.get PNHALT).length = bs.length) :
    ((Cmd.forBnd I2 PNHALT haltBody).eval s).get SCAN = encSyms rest
    ∧ ((Cmd.forBnd I2 PNHALT haltBody).eval s).get PHALT = bs.map bitOf := by
  rw [Cmd.eval_forBnd, hbnd]
  have key := Cmd.foldlState_range_induct haltBody I2 bs.length s
    (fun i t => t.get SCAN = encSyms ((bs.drop i).map bitOf ++ rest)
      ∧ t.get PHALT = (bs.take i).map bitOf)
    ⟨by simpa using hSCAN, by simpa using hPH⟩
    (fun i t hi hM => haltBody_step bs rest i hi t hM.1 hM.2)
  simpa using key


/-! ### Stage P's run lemma -/

/-- The machine stream in cons form (what the five header reads consume). -/
theorem flattenTM_cons (M : FlatTM) :
    flattenTM M
      = M.sig :: M.tapes :: M.states :: M.start :: M.halt.length ::
          (M.halt.map bitOf ++ M.trans.length :: transFlat M) := by
  rw [flattenTM_eq]
  simp [bitOf]

/-! Each suffix peels one command. Proved by `rw [Cmd.eval_seq]` rather than
`rfl`: `Cmd.eval` is `Cmd.run`, so a `rfl` here asks `whnf` to *evaluate* the
loops symbolically and times out. -/

private theorem stageP_eval (s : State) :
    stageP.eval s = pSuf1.eval ((Cmd.op (.copy SCAN MREG)).eval s) := by
  unfold stageP; rw [Cmd.eval_seq]

private theorem pSuf1_eval (s : State) :
    pSuf1.eval s = pSuf2.eval ((readItem PSIG SCAN I1).eval s) := by
  unfold pSuf1; rw [Cmd.eval_seq]

private theorem pSuf2_eval (s : State) :
    pSuf2.eval s = pSuf3.eval ((readItem PTAPES SCAN I1).eval s) := by
  unfold pSuf2; rw [Cmd.eval_seq]

private theorem pSuf3_eval (s : State) :
    pSuf3.eval s = pSuf4.eval ((readItem PSTATES SCAN I1).eval s) := by
  unfold pSuf3; rw [Cmd.eval_seq]

private theorem pSuf4_eval (s : State) :
    pSuf4.eval s = pSuf5.eval ((readItem PSTART SCAN I1).eval s) := by
  unfold pSuf4; rw [Cmd.eval_seq]

private theorem pSuf5_eval (s : State) :
    pSuf5.eval s = pSuf6.eval ((readItem PNHALT SCAN I1).eval s) := by
  unfold pSuf5; rw [Cmd.eval_seq]

private theorem pSuf6_eval (s : State) :
    pSuf6.eval s = pSuf7.eval ((Cmd.op (.clear PHALT)).eval s) := by
  unfold pSuf6; rw [Cmd.eval_seq]

private theorem pSuf7_eval (s : State) :
    pSuf7.eval s = pSuf8.eval ((Cmd.forBnd I2 PNHALT haltBody).eval s) := by
  unfold pSuf7; rw [Cmd.eval_seq]

private theorem pSuf8_eval (s : State) :
    pSuf8.eval s = pSuf9.eval ((readItem PNTRANS SCAN I1).eval s) := by
  unfold pSuf8; rw [Cmd.eval_seq]

/-- **Stage P is correct.** No validity hypothesis: `flattenEntry` writes each
list's own length before its payload, so the parse is data-driven and never
desynchronises (see the module docstring). -/
theorem stageP_run (M : FlatTM) (st : State)
    (hM : st.get MREG = encSyms (flattenTM M)) :
    (stageP.eval st).get PSIG = List.replicate M.sig 1
    ∧ (stageP.eval st).get PTAPES = List.replicate M.tapes 1
    ∧ (stageP.eval st).get PSTATES = List.replicate M.states 1
    ∧ (stageP.eval st).get PSTART = List.replicate M.start 1
    ∧ (stageP.eval st).get PNHALT = List.replicate M.halt.length 1
    ∧ (stageP.eval st).get PHALT = M.halt.map bitOf
    ∧ (stageP.eval st).get PNTRANS = List.replicate M.trans.length 1
    ∧ (stageP.eval st).get PTRANS = encSyms (transFlat M) := by
  set tl : List Nat := M.halt.map bitOf ++ M.trans.length :: transFlat M with htl
  -- step 0: the cursor copy
  have hc1 : stageP.eval st = pSuf1.eval ((Cmd.op (.copy SCAN MREG)).eval st) :=
    stageP_eval st
  have hb0 : ((Cmd.op (.copy SCAN MREG)).eval st).get SCAN
      = encSyms (M.sig :: (M.tapes :: M.states :: M.start :: M.halt.length :: tl)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hM, flattenTM_cons, htl]
  set b0 := (Cmd.op (.copy SCAN MREG)).eval st with hb0d
  -- step 1: sig
  obtain ⟨h1a, h1b⟩ := readItem_run b0 M.sig _ PSIG SCAN I1 (by decide) hb0
  have hc2 : stageP.eval st = pSuf2.eval ((readItem PSIG SCAN I1).eval b0) :=
    hc1.trans (pSuf1_eval b0)
  set b1 := (readItem PSIG SCAN I1).eval b0 with hb1d
  -- step 2: tapes
  obtain ⟨h2a, h2b⟩ := readItem_run b1 M.tapes _ PTAPES SCAN I1 (by decide) h1b
  have hc3 : stageP.eval st = pSuf3.eval ((readItem PTAPES SCAN I1).eval b1) :=
    hc2.trans (pSuf2_eval b1)
  set b2 := (readItem PTAPES SCAN I1).eval b1 with hb2d
  -- step 3: states
  obtain ⟨h3a, h3b⟩ := readItem_run b2 M.states _ PSTATES SCAN I1 (by decide) h2b
  have hc4 : stageP.eval st = pSuf4.eval ((readItem PSTATES SCAN I1).eval b2) :=
    hc3.trans (pSuf3_eval b2)
  set b3 := (readItem PSTATES SCAN I1).eval b2 with hb3d
  -- step 4: start
  obtain ⟨h4a, h4b⟩ := readItem_run b3 M.start _ PSTART SCAN I1 (by decide) h3b
  have hc5 : stageP.eval st = pSuf5.eval ((readItem PSTART SCAN I1).eval b3) :=
    hc4.trans (pSuf4_eval b3)
  set b4 := (readItem PSTART SCAN I1).eval b3 with hb4d
  -- step 5: |halt|
  obtain ⟨h5a, h5b⟩ := readItem_run b4 M.halt.length _ PNHALT SCAN I1 (by decide) h4b
  have hc6 : stageP.eval st = pSuf6.eval ((readItem PNHALT SCAN I1).eval b4) :=
    hc5.trans (pSuf5_eval b4)
  set b5 := (readItem PNHALT SCAN I1).eval b4 with hb5d
  -- step 6: clear PHALT
  have hc7 : stageP.eval st = pSuf7.eval ((Cmd.op (.clear PHALT)).eval b5) :=
    hc6.trans (pSuf6_eval b5)
  have h6P : ((Cmd.op (.clear PHALT)).eval b5).get PHALT = [] := by
    rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
  have h6S : ((Cmd.op (.clear PHALT)).eval b5).get SCAN = encSyms tl := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (SCAN : Var) ≠ PHALT)]
    exact h5b
  have h6N : (((Cmd.op (.clear PHALT)).eval b5).get PNHALT).length = M.halt.length := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (PNHALT : Var) ≠ PHALT)]
    rw [h5a, List.length_replicate]
  set b6 := (Cmd.op (.clear PHALT)).eval b5 with hb6d
  -- step 7: the halt-bit loop
  obtain ⟨h7S, h7P⟩ := haltLoop_run M.halt (M.trans.length :: transFlat M) b6
    (by rw [h6S, htl]) h6P h6N
  have hc8 : stageP.eval st = pSuf8.eval ((Cmd.forBnd I2 PNHALT haltBody).eval b6) :=
    hc7.trans (pSuf7_eval b6)
  set b7 := (Cmd.forBnd I2 PNHALT haltBody).eval b6 with hb7d
  -- step 8: |trans|
  obtain ⟨h8a, h8b⟩ := readItem_run b7 M.trans.length _ PNTRANS SCAN I1 (by decide) h7S
  have hc9 : stageP.eval st = pSuf9.eval ((readItem PNTRANS SCAN I1).eval b7) :=
    hc8.trans (pSuf8_eval b7)
  set b8 := (readItem PNTRANS SCAN I1).eval b7 with hb8d
  -- step 9: the transition sub-stream
  have h9T : (pSuf9.eval b8).get PTRANS = encSyms (transFlat M) := by
    show ((Cmd.op (.copy PTRANS SCAN)).eval b8).get PTRANS = _
    rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact h8b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2, Cmd.eval_get_of_not_writes pSuf2 b1 PSIG (by decide)]; exact h1a
  · rw [hc3, Cmd.eval_get_of_not_writes pSuf3 b2 PTAPES (by decide)]; exact h2a
  · rw [hc4, Cmd.eval_get_of_not_writes pSuf4 b3 PSTATES (by decide)]; exact h3a
  · rw [hc5, Cmd.eval_get_of_not_writes pSuf5 b4 PSTART (by decide)]; exact h4a
  · rw [hc6, Cmd.eval_get_of_not_writes pSuf6 b5 PNHALT (by decide)]; exact h5a
  · rw [hc8, Cmd.eval_get_of_not_writes pSuf8 b7 PHALT (by decide)]; exact h7P
  · rw [hc9, Cmd.eval_get_of_not_writes pSuf9 b8 PNTRANS (by decide)]; exact h8a
  · rw [hc9]; exact h9T


/-! ## Stage G — the guard

`FLG` carries the running conjunction (`[1]` = true, `[]` = false). Each check
writes its verdict bit to `RES` and `andIn` folds it in; `ZERO` (register `0`)
is the no-op target of the true branch, so `andIn` never touches anything else.
-/

/-- The no-op: clear the always-empty register `0`. -/
def nop : Cmd := Cmd.op (.clear ZERO)

/-- AND the verdict bit in `RES` into the running flag `FLG`. -/
def andIn : Cmd := Cmd.ifBit RES nop (Cmd.op (.clear FLG))

/-- `FLG := FLG && (|A| < |B|)`. -/
def ltCheck (A B idx : Var) : Cmd := CliqueRelTM.ltBit RES A B idx ;; andIn

/-- `FLG := FLG && (A = B)` (both unary). -/
def eqCheck (A B : Var) : Cmd := Cmd.op (.eqBit RES A B) ;; andIn

theorem andIn_run (p q : Bool) (s : State)
    (hR : s.get RES = [if q then 1 else 0])
    (hF : s.get FLG = (if p then [1] else [])) :
    (andIn.eval s).get FLG = (if p && q then [1] else []) := by
  unfold andIn
  cases q with
  | true =>
      have h1 : s.get RES = [1] := by rw [hR]; rfl
      rw [Cmd.eval_ifBit_true _ _ _ _ h1]
      show ((Cmd.op (.clear ZERO)).eval s).get FLG = _
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (FLG : Var) ≠ ZERO),
        hF, Bool.and_true]
  | false =>
      have h1 : s.get RES ≠ [1] := by rw [hR]; decide
      rw [Cmd.eval_ifBit_false _ _ _ _ h1, Cmd.eval_op]
      simp [Op.eval, State.get_set_eq]

/-- **`ltCheck` is correct.** -/
theorem ltCheck_run (A B idx : Var) (a b : Nat) (p : Bool) (s : State)
    (hALT : A ≠ CliqueRelTM.LT_B) (hidx : idx ≠ CliqueRelTM.LT_B)
    (hiF : idx ≠ FLG)
    (hA : s.get A = List.replicate a 1) (hB : s.get B = List.replicate b 1)
    (hF : s.get FLG = (if p then [1] else [])) :
    ((ltCheck A B idx).eval s).get FLG = (if p && decide (a < b) then [1] else []) := by
  obtain ⟨hlt, hfr⟩ := CliqueRelTM.ltBit_run s a b RES A B idx hA hB hALT hidx
  have hFmid : ((CliqueRelTM.ltBit RES A B idx).eval s).get FLG
      = (if p then [1] else []) := by
    rw [hfr FLG (by decide) (Ne.symm hiF) (by decide)]; exact hF
  have hRmid : ((CliqueRelTM.ltBit RES A B idx).eval s).get RES
      = [if decide (a < b) then 1 else 0] := by
    rw [hlt]; by_cases h : a < b <;> simp [h]
  unfold ltCheck
  rw [Cmd.eval_seq]
  exact andIn_run p (decide (a < b)) _ hRmid hFmid

/-- **`eqCheck` is correct.** -/
theorem eqCheck_run (A B : Var) (a b : Nat) (p : Bool) (s : State)
    (hA : s.get A = List.replicate a 1) (hB : s.get B = List.replicate b 1)
    (hF : s.get FLG = (if p then [1] else [])) :
    ((eqCheck A B).eval s).get FLG = (if p && decide (a = b) then [1] else []) := by
  have hRmid : ((Cmd.op (.eqBit RES A B)).eval s).get RES
      = [if decide (a = b) then 1 else 0] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, hA, hB]
    by_cases h : a = b
    · rw [if_pos (by rw [h]), if_pos (by simpa using h)]
    · rw [if_neg (fun hh => h (CliqueRelTM.replicate_one_eq_iff.mp hh)),
        if_neg (by simpa using h)]
  have hFmid : ((Cmd.op (.eqBit RES A B)).eval s).get FLG = (if p then [1] else []) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (FLG : Var) ≠ RES)]
    exact hF
  unfold eqCheck
  rw [Cmd.eval_seq]
  exact andIn_run p (decide (a = b)) _ hRmid hFmid


/-! ### The scan invariant

Stage G threads exactly five registers through the transition scan: the cursor
`TSCAN`, the flag `FLG`, and P's three read-only parameters. Bundling them makes
each of the thirteen steps of `entryBody` a one-line invariant transport. -/

/-- The stage-G scan invariant: cursor at `str`, flag at `b`, parameters live. -/
def EInv (M : flatTM) (str : List Nat) (b : Bool) (s : State) : Prop :=
  s.get TSCAN = encSyms str
  ∧ s.get FLG = (if b then [1] else [])
  ∧ s.get PSIG = List.replicate M.sig 1
  ∧ s.get PSTATES = List.replicate M.states 1
  ∧ s.get PTAPES = List.replicate M.tapes 1

theorem EInv_set (M : flatTM) (str : List Nat) (b : Bool) (s : State)
    (r : Var) (v : List Nat)
    (h1 : r ≠ TSCAN) (h2 : r ≠ FLG) (h3 : r ≠ PSIG) (h4 : r ≠ PSTATES)
    (h5 : r ≠ PTAPES) (h : EInv M str b s) : EInv M str b (s.set r v) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  exact ⟨by rw [State.get_set_ne _ _ _ _ (Ne.symm h1)]; exact e1,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h2)]; exact e2,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h3)]; exact e3,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h4)]; exact e4,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h5)]; exact e5⟩

/-- Transport the invariant across a command that writes none of its registers
(discharge the five memberships with `by decide`). -/
theorem EInv_frame (c : Cmd) (M : flatTM) (str : List Nat) (b : Bool) (s : State)
    (h1 : TSCAN ∉ c.writes) (h2 : FLG ∉ c.writes) (h3 : PSIG ∉ c.writes)
    (h4 : PSTATES ∉ c.writes) (h5 : PTAPES ∉ c.writes)
    (h : EInv M str b s) : EInv M str b (c.eval s) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  exact ⟨by rw [Cmd.eval_get_of_not_writes c s TSCAN h1]; exact e1,
    by rw [Cmd.eval_get_of_not_writes c s FLG h2]; exact e2,
    by rw [Cmd.eval_get_of_not_writes c s PSIG h3]; exact e3,
    by rw [Cmd.eval_get_of_not_writes c s PSTATES h4]; exact e4,
    by rw [Cmd.eval_get_of_not_writes c s PTAPES h5]; exact e5⟩

/-! ### The three step gadgets -/

/-- Read the next item of the transition stream into `VAL`. -/
theorem readVal_step (M : flatTM) (v : Nat) (str : List Nat) (b : Bool) (s : State)
    (h : EInv M (v :: str) b s) :
    EInv M str b ((readItem VAL TSCAN I2).eval s)
    ∧ ((readItem VAL TSCAN I2).eval s).get VAL = List.replicate v 1 := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  obtain ⟨hval, hscan⟩ := readItem_run s v str VAL TSCAN I2 (by decide) e1
  refine ⟨⟨hscan, ?_, ?_, ?_, ?_⟩, hval⟩
  · rw [Cmd.eval_get_of_not_writes _ s FLG (by decide)]; exact e2
  · rw [Cmd.eval_get_of_not_writes _ s PSIG (by decide)]; exact e3
  · rw [Cmd.eval_get_of_not_writes _ s PSTATES (by decide)]; exact e4
  · rw [Cmd.eval_get_of_not_writes _ s PTAPES (by decide)]; exact e5

/-- `FLG &&= (VAL < states)`. -/
theorem ltStates_step (M : flatTM) (a : Nat) (str : List Nat) (b : Bool) (s : State)
    (hV : s.get VAL = List.replicate a 1) (h : EInv M str b s) :
    EInv M str (b && decide (a < M.states)) ((ltCheck VAL PSTATES I3).eval s) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  refine ⟨?_, ltCheck_run VAL PSTATES I3 a M.states b s (by decide) (by decide)
      (by decide) hV e4 e2, ?_, ?_, ?_⟩
  · rw [Cmd.eval_get_of_not_writes _ s TSCAN (by decide)]; exact e1
  · rw [Cmd.eval_get_of_not_writes _ s PSIG (by decide)]; exact e3
  · rw [Cmd.eval_get_of_not_writes _ s PSTATES (by decide)]; exact e4
  · rw [Cmd.eval_get_of_not_writes _ s PTAPES (by decide)]; exact e5

/-- `FLG &&= (VAL < sig)`. -/
theorem ltSig_step (M : flatTM) (a : Nat) (str : List Nat) (b : Bool) (s : State)
    (idx : Var) (hidx : idx = I5 ∨ idx = I3)
    (hV : s.get VAL = List.replicate a 1) (h : EInv M str b s) :
    EInv M str (b && decide (a < M.sig)) ((ltCheck VAL PSIG idx).eval s) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  rcases hidx with rfl | rfl
  · refine ⟨?_, ltCheck_run VAL PSIG I5 a M.sig b s (by decide) (by decide)
        (by decide) hV e3 e2, ?_, ?_, ?_⟩
    · rw [Cmd.eval_get_of_not_writes _ s TSCAN (by decide)]; exact e1
    · rw [Cmd.eval_get_of_not_writes _ s PSIG (by decide)]; exact e3
    · rw [Cmd.eval_get_of_not_writes _ s PSTATES (by decide)]; exact e4
    · rw [Cmd.eval_get_of_not_writes _ s PTAPES (by decide)]; exact e5
  · refine ⟨?_, ltCheck_run VAL PSIG I3 a M.sig b s (by decide) (by decide)
        (by decide) hV e3 e2, ?_, ?_, ?_⟩
    · rw [Cmd.eval_get_of_not_writes _ s TSCAN (by decide)]; exact e1
    · rw [Cmd.eval_get_of_not_writes _ s PSIG (by decide)]; exact e3
    · rw [Cmd.eval_get_of_not_writes _ s PSTATES (by decide)]; exact e4
    · rw [Cmd.eval_get_of_not_writes _ s PTAPES (by decide)]; exact e5

/-- `FLG &&= (VAL = tapes)`. -/
theorem eqTapes_step (M : flatTM) (a : Nat) (str : List Nat) (b : Bool) (s : State)
    (hV : s.get VAL = List.replicate a 1) (h : EInv M str b s) :
    EInv M str (b && decide (a = M.tapes)) ((eqCheck VAL PTAPES).eval s) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  refine ⟨?_, eqCheck_run VAL PTAPES a M.tapes b s hV e5 e2, ?_, ?_, ?_⟩
  · rw [Cmd.eval_get_of_not_writes _ s TSCAN (by decide)]; exact e1
  · rw [Cmd.eval_get_of_not_writes _ s PSIG (by decide)]; exact e3
  · rw [Cmd.eval_get_of_not_writes _ s PSTATES (by decide)]; exact e4
  · rw [Cmd.eval_get_of_not_writes _ s PTAPES (by decide)]; exact e5


/-! ### List helpers for the scan loops -/

private theorem drop_flatMap_cons {α : Type} (f : α → List Nat) (l : List α) (i : Nat)
    (hi : i < l.length) :
    (l.drop i).flatMap f = f (l[i]'hi) ++ (l.drop (i + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]

private theorem drop_cons_self {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = (l[i]'hi) :: l.drop (i + 1) := List.drop_eq_getElem_cons hi

private theorem all_take_succ {α : Type} (f : α → Bool) (l : List α) (i : Nat)
    (hi : i < l.length) :
    (l.take (i + 1)).all f = ((l.take i).all f && f (l[i]'hi)) := by
  have ht : l.take (i + 1) = l.take i ++ [l[i]'hi] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [ht, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-! ### One `Option Nat` item pair -/

/-- Consume one `encOptN` item group (`0` for `none`, `1 v` for `some v`) and
AND its symbol-bound verdict into `FLG`. This is the variable-arity core of the
whole parse. -/
def optCheck : Cmd :=
  readItem VAL TSCAN I2 ;;
  Cmd.op (.nonEmpty NEF VAL) ;;
  Cmd.ifBit NEF (readItem VAL TSCAN I2 ;; ltCheck VAL PSIG I5) nop

theorem optCheck_run (M : flatTM) (o : Option Nat) (str : List Nat) (b : Bool)
    (s : State) (h : EInv M (encOptN o ++ str) b s) :
    EInv M str (b && isSomeNatBelow M.sig o) (optCheck.eval s) := by
  have hev : optCheck.eval s
      = (Cmd.ifBit NEF (readItem VAL TSCAN I2 ;; ltCheck VAL PSIG I5) nop).eval
          ((Cmd.op (.nonEmpty NEF VAL)).eval ((readItem VAL TSCAN I2).eval s)) := by
    unfold optCheck; rw [Cmd.eval_seq, Cmd.eval_seq]
  cases o with
  | none =>
      have h0 : EInv M (0 :: str) b s := h
      obtain ⟨hE1, hV1⟩ := readVal_step M 0 str b s h0
      have hNE : ((Cmd.op (.nonEmpty NEF VAL)).eval
          ((readItem VAL TSCAN I2).eval s)).get NEF ≠ [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hV1]; decide
      have hE2 : EInv M str b ((Cmd.op (.nonEmpty NEF VAL)).eval
          ((readItem VAL TSCAN I2).eval s)) :=
        EInv_frame _ M str b _ (by decide) (by decide) (by decide) (by decide)
          (by decide) hE1
      rw [hev, Cmd.eval_ifBit_false _ _ _ _ hNE]
      show EInv M str (b && true) _
      rw [Bool.and_true]
      exact EInv_frame nop M str b _ (by decide) (by decide) (by decide) (by decide)
        (by decide) hE2
  | some v =>
      have h0 : EInv M (1 :: v :: str) b s := h
      obtain ⟨hE1, hV1⟩ := readVal_step M 1 (v :: str) b s h0
      have hNE : ((Cmd.op (.nonEmpty NEF VAL)).eval
          ((readItem VAL TSCAN I2).eval s)).get NEF = [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hV1]; rfl
      have hE2 : EInv M (v :: str) b ((Cmd.op (.nonEmpty NEF VAL)).eval
          ((readItem VAL TSCAN I2).eval s)) :=
        EInv_frame _ M (v :: str) b _ (by decide) (by decide) (by decide) (by decide)
          (by decide) hE1
      rw [hev, Cmd.eval_ifBit_true _ _ _ _ hNE, Cmd.eval_seq]
      obtain ⟨hE3, hV3⟩ := readVal_step M v str b _ hE2
      show EInv M str (b && decide (v < M.sig)) _
      exact ltSig_step M v str b _ I5 (Or.inl rfl) hV3 hE3

/-! ### The option-list loop and the move-skip loop

Both are `forBnd` over the arity just parsed into `VAL`; `forBnd` reads its
bound's length once at entry, so the body may (and does) overwrite `VAL`. -/

def optLoop : Cmd := Cmd.forBnd I4 VAL optCheck
def skipLoop : Cmd := Cmd.forBnd I4 VAL (readItem VAL TSCAN I2)

theorem optLoop_run (M : flatTM) (l : List (Option Nat)) (str : List Nat) (b : Bool)
    (s : State) (hV : (s.get VAL).length = l.length)
    (h : EInv M (optsFlat l ++ str) b s) :
    EInv M str (b && l.all (isSomeNatBelow M.sig)) (optLoop.eval s) := by
  unfold optLoop
  rw [Cmd.eval_forBnd, hV]
  have key := Cmd.foldlState_range_induct optCheck I4 l.length s
    (fun i t => EInv M ((l.drop i).flatMap encOptN ++ str)
      (b && (l.take i).all (isSomeNatBelow M.sig)) t)
    (by simpa [optsFlat] using h)
    (by
      intro i t hi hM
      have hset := EInv_set M _ _ _ I4 (List.replicate i 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) hM
      rw [drop_flatMap_cons encOptN l i hi, List.append_assoc] at hset
      have := optCheck_run M (l[i]'hi) ((l.drop (i+1)).flatMap encOptN ++ str) _ _ hset
      rw [all_take_succ (isSomeNatBelow M.sig) l i hi, ← Bool.and_assoc]
      exact this)
  simpa using key

theorem skipLoop_run (M : flatTM) (xs : List Nat) (str : List Nat) (b : Bool)
    (s : State) (hV : (s.get VAL).length = xs.length)
    (h : EInv M (xs ++ str) b s) :
    EInv M str b (skipLoop.eval s) := by
  unfold skipLoop
  rw [Cmd.eval_forBnd, hV]
  have key := Cmd.foldlState_range_induct (readItem VAL TSCAN I2) I4 xs.length s
    (fun i t => EInv M (xs.drop i ++ str) b t)
    (by simpa using h)
    (by
      intro i t hi hM
      have hset := EInv_set M _ _ _ I4 (List.replicate i 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) hM
      rw [drop_cons_self xs i hi, List.cons_append] at hset
      exact (readVal_step M (xs[i]'hi) (xs.drop (i+1) ++ str) b _ hset).1)
  simpa using key


/-! ### One transition entry

`flattenEntry` lays an entry out as three field groups, so `entryBody` is a
five-step chain of three small gadgets. -/

/-- A state-index field: read it, check `< states`. -/
def fieldCheck : Cmd := readItem VAL TSCAN I2 ;; ltCheck VAL PSTATES I3

/-- An arity field followed by its `Option Nat` list: check the arity against
`tapes`, then every symbol against `sig`. -/
def arityOptCheck : Cmd :=
  readItem VAL TSCAN I2 ;; eqCheck VAL PTAPES ;; optLoop

/-- The move-list arity field: check it against `tapes`, then skip the moves. -/
def arityMoveCheck : Cmd :=
  readItem VAL TSCAN I2 ;; eqCheck VAL PTAPES ;; skipLoop

def eSuf4 : Cmd := arityOptCheck ;; arityMoveCheck
def eSuf3 : Cmd := fieldCheck ;; eSuf4
def eSuf2 : Cmd := arityOptCheck ;; eSuf3

/-- One transition entry: the whole per-entry conjunct of `isValidFlatTM`. -/
def entryBody : Cmd := fieldCheck ;; eSuf2

/-- The per-entry validity `Bool` **in program order** (the stream dictates the
order; `entryPB_eq` reconciles it with `isValidFlatTM`'s). -/
def entryPB (M : flatTM) (e : FlatTMTransEntry) : Bool :=
  decide (e.src_state < M.states) &&
  decide (e.src_tape_vals.length = M.tapes) &&
  e.src_tape_vals.all (isSomeNatBelow M.sig) &&
  decide (e.dst_state < M.states) &&
  decide (e.dst_write_vals.length = M.tapes) &&
  e.dst_write_vals.all (isSomeNatBelow M.sig) &&
  decide (e.move_dirs.length = M.tapes)

theorem fieldCheck_run (M : flatTM) (q : Nat) (str : List Nat) (b : Bool) (s : State)
    (h : EInv M (q :: str) b s) :
    EInv M str (b && decide (q < M.states)) (fieldCheck.eval s) := by
  have hev : fieldCheck.eval s
      = (ltCheck VAL PSTATES I3).eval ((readItem VAL TSCAN I2).eval s) := by
    unfold fieldCheck; rw [Cmd.eval_seq]
  obtain ⟨hE1, hV1⟩ := readVal_step M q str b s h
  rw [hev]
  exact ltStates_step M q str b _ hV1 hE1

theorem arityOptCheck_run (M : flatTM) (l : List (Option Nat)) (str : List Nat)
    (b : Bool) (s : State)
    (h : EInv M (l.length :: (optsFlat l ++ str)) b s) :
    EInv M str (b && decide (l.length = M.tapes) && l.all (isSomeNatBelow M.sig))
      (arityOptCheck.eval s) := by
  have hev : arityOptCheck.eval s
      = optLoop.eval ((eqCheck VAL PTAPES).eval ((readItem VAL TSCAN I2).eval s)) := by
    unfold arityOptCheck; rw [Cmd.eval_seq, Cmd.eval_seq]
  obtain ⟨hE1, hV1⟩ := readVal_step M l.length (optsFlat l ++ str) b s h
  have hE2 := eqTapes_step M l.length (optsFlat l ++ str) b _ hV1 hE1
  have hV2 : ((eqCheck VAL PTAPES).eval ((readItem VAL TSCAN I2).eval s)).get VAL
      = List.replicate l.length 1 := by
    rw [Cmd.eval_get_of_not_writes _ _ VAL (by decide)]; exact hV1
  rw [hev]
  exact optLoop_run M l str _ _ (by rw [hV2, List.length_replicate]) hE2

theorem arityMoveCheck_run (M : flatTM) (ms : List TMMove) (str : List Nat)
    (b : Bool) (s : State)
    (h : EInv M (ms.length :: (ms.map encMoveN ++ str)) b s) :
    EInv M str (b && decide (ms.length = M.tapes)) (arityMoveCheck.eval s) := by
  have hev : arityMoveCheck.eval s
      = skipLoop.eval ((eqCheck VAL PTAPES).eval ((readItem VAL TSCAN I2).eval s)) := by
    unfold arityMoveCheck; rw [Cmd.eval_seq, Cmd.eval_seq]
  obtain ⟨hE1, hV1⟩ := readVal_step M ms.length (ms.map encMoveN ++ str) b s h
  have hE2 := eqTapes_step M ms.length (ms.map encMoveN ++ str) b _ hV1 hE1
  have hV2 : ((eqCheck VAL PTAPES).eval ((readItem VAL TSCAN I2).eval s)).get VAL
      = List.replicate ms.length 1 := by
    rw [Cmd.eval_get_of_not_writes _ _ VAL (by decide)]; exact hV1
  rw [hev]
  exact skipLoop_run M (ms.map encMoveN) str _ _
    (by rw [hV2, List.length_replicate, List.length_map]) hE2

/-- The entry stream in the cons form the five steps consume. -/
theorem flattenEntry_append (e : FlatTMTransEntry) (str : List Nat) :
    flattenEntry e ++ str
      = e.src_state :: e.src_tape_vals.length ::
          (optsFlat e.src_tape_vals ++ e.dst_state :: e.dst_write_vals.length ::
            (optsFlat e.dst_write_vals ++ e.move_dirs.length ::
              (e.move_dirs.map encMoveN ++ str))) := by
  rw [flattenEntry_eq]
  simp

private theorem and8_assoc (b c1 c2 c3 c4 c5 c6 c7 : Bool) :
    (b && c1 && c2 && c3 && c4 && c5 && c6 && c7)
      = (b && (c1 && c2 && c3 && c4 && c5 && c6 && c7)) := by
  simp only [Bool.and_assoc]

/-- **One entry is checked correctly** (and the cursor lands exactly past it). -/
theorem entryBody_run (M : flatTM) (e : FlatTMTransEntry) (str : List Nat)
    (b : Bool) (s : State) (h : EInv M (flattenEntry e ++ str) b s) :
    EInv M str (b && entryPB M e) (entryBody.eval s) := by
  rw [flattenEntry_append] at h
  have hev : entryBody.eval s = eSuf2.eval (fieldCheck.eval s) := by
    unfold entryBody; rw [Cmd.eval_seq]
  have h1 := fieldCheck_run M e.src_state _ b s h
  have hev2 : eSuf2.eval (fieldCheck.eval s)
      = eSuf3.eval (arityOptCheck.eval (fieldCheck.eval s)) := by
    unfold eSuf2; rw [Cmd.eval_seq]
  have h2 := arityOptCheck_run M e.src_tape_vals _ _ _ h1
  have hev3 : eSuf3.eval (arityOptCheck.eval (fieldCheck.eval s))
      = eSuf4.eval (fieldCheck.eval (arityOptCheck.eval (fieldCheck.eval s))) := by
    unfold eSuf3; rw [Cmd.eval_seq]
  have h3 := fieldCheck_run M e.dst_state _ _ _ h2
  have hev4 : eSuf4.eval (fieldCheck.eval (arityOptCheck.eval (fieldCheck.eval s)))
      = arityMoveCheck.eval (arityOptCheck.eval
          (fieldCheck.eval (arityOptCheck.eval (fieldCheck.eval s)))) := by
    unfold eSuf4; rw [Cmd.eval_seq]
  have h4 := arityOptCheck_run M e.dst_write_vals _ _ _ h3
  have h5 := arityMoveCheck_run M e.move_dirs str _ _ h4
  rw [hev, hev2, hev3, hev4]
  unfold entryPB
  rw [← and8_assoc]
  exact h5


/-! ### The transition-table loop -/

def entryLoop : Cmd := Cmd.forBnd I1 PNTRANS entryBody

theorem entryLoop_run (M : flatTM) (b : Bool) (s : State)
    (hN : (s.get PNTRANS).length = M.trans.length)
    (h : EInv M (transFlat M) b s) :
    EInv M [] (b && M.trans.all (entryPB M)) (entryLoop.eval s) := by
  unfold entryLoop
  rw [Cmd.eval_forBnd, hN]
  have key := Cmd.foldlState_range_induct entryBody I1 M.trans.length s
    (fun i t => EInv M ((M.trans.drop i).flatMap flattenEntry)
      (b && (M.trans.take i).all (entryPB M)) t)
    (by simpa [transFlat] using h)
    (by
      intro i t hi hM
      have hset := EInv_set M _ _ _ I1 (List.replicate i 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) hM
      rw [drop_flatMap_cons flattenEntry M.trans i hi] at hset
      have := entryBody_run M (M.trans[i]'hi)
        ((M.trans.drop (i+1)).flatMap flattenEntry) _ _ hset
      rw [all_take_succ (entryPB M) M.trans i hi, ← Bool.and_assoc]
      exact this)
  simpa using key

/-- `encSyms` never shrinks a list: at least one cell per item (in fact two).
Local to this file — `S1Witness.encSyms_length` proves the exact identity, but
`S1Parse` sits *below* `S1Witness` in the import order. -/
private theorem encSyms_length_ge (l : List Nat) : l.length ≤ (encSyms l).length := by
  induction l with
  | nil => simp [encSyms_nil]
  | cons v vs ih =>
      rw [encSyms_cons']
      simp only [List.length_cons, List.length_append, List.length_replicate]
      omega

/-! ### The input-string loop

The bound register is the *string stream itself* (`|encSyms str| ≥ |str|`), so
the loop runs a few idle iterations after the last item; the `nonEmpty` guard
makes those no-ops. The invariant is stated with `drop`/`take`, which absorb
`i ≥ |str|` for free. -/

/-- The input-string scan invariant. -/
def SInv (M : flatTM) (l : List Nat) (b : Bool) (s : State) : Prop :=
  s.get SCAN = encSyms l
  ∧ s.get FLG = (if b then [1] else [])
  ∧ s.get PSIG = List.replicate M.sig 1

def sBody : Cmd :=
  Cmd.op (.nonEmpty NEF SCAN) ;;
  Cmd.ifBit NEF (readItem VAL SCAN I2 ;; ltCheck VAL PSIG I3) nop

def sLoop : Cmd := Cmd.op (.copy SCAN SREG) ;; Cmd.forBnd I1 SREG sBody

private theorem SInv_set (M : flatTM) (l : List Nat) (b : Bool) (s : State)
    (r : Var) (v : List Nat) (h1 : r ≠ SCAN) (h2 : r ≠ FLG) (h3 : r ≠ PSIG)
    (h : SInv M l b s) : SInv M l b (s.set r v) := by
  obtain ⟨e1, e2, e3⟩ := h
  exact ⟨by rw [State.get_set_ne _ _ _ _ (Ne.symm h1)]; exact e1,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h2)]; exact e2,
    by rw [State.get_set_ne _ _ _ _ (Ne.symm h3)]; exact e3⟩

private theorem SInv_frame (c : Cmd) (M : flatTM) (l : List Nat) (b : Bool) (s : State)
    (h1 : SCAN ∉ c.writes) (h2 : FLG ∉ c.writes) (h3 : PSIG ∉ c.writes)
    (h : SInv M l b s) : SInv M l b (c.eval s) := by
  obtain ⟨e1, e2, e3⟩ := h
  exact ⟨by rw [Cmd.eval_get_of_not_writes c s SCAN h1]; exact e1,
    by rw [Cmd.eval_get_of_not_writes c s FLG h2]; exact e2,
    by rw [Cmd.eval_get_of_not_writes c s PSIG h3]; exact e3⟩

private theorem sBody_step (M : flatTM) (l : List Nat) (b : Bool) (i : Nat) (t : State)
    (h : SInv M (l.drop i) (b && (l.take i).all (fun x => decide (x < M.sig))) t) :
    SInv M (l.drop (i + 1)) (b && (l.take (i + 1)).all (fun x => decide (x < M.sig)))
      (sBody.eval (t.set I1 (List.replicate i 1))) := by
  have hset := SInv_set M _ _ _ I1 (List.replicate i 1)
    (by decide) (by decide) (by decide) h
  set u := t.set I1 (List.replicate i 1) with hu
  have hev : sBody.eval u
      = (Cmd.ifBit NEF (readItem VAL SCAN I2 ;; ltCheck VAL PSIG I3) nop).eval
          ((Cmd.op (.nonEmpty NEF SCAN)).eval u) := by
    unfold sBody; rw [Cmd.eval_seq]
  obtain ⟨e1, e2, e3⟩ := hset
  by_cases hi : i < l.length
  · -- a live iteration
    rw [drop_cons_self l i hi] at e1
    have hne : ((Cmd.op (.nonEmpty NEF SCAN)).eval u).get NEF = [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, e1, encSyms_cons']
      rfl
    have hS2 : SInv M ((l[i]'hi) :: l.drop (i+1))
        (b && (l.take i).all (fun x => decide (x < M.sig)))
        ((Cmd.op (.nonEmpty NEF SCAN)).eval u) :=
      SInv_frame _ M _ _ u (by decide) (by decide) (by decide) ⟨e1, e2, e3⟩
    obtain ⟨f1, f2, f3⟩ := hS2
    obtain ⟨hval, hscan⟩ := readItem_run _ (l[i]'hi) (l.drop (i+1)) VAL SCAN I2
      (by decide) f1
    have hF3 : ((readItem VAL SCAN I2).eval ((Cmd.op (.nonEmpty NEF SCAN)).eval u)).get FLG
        = _ := Cmd.eval_get_of_not_writes _ _ FLG (by decide)
    have hP3 : ((readItem VAL SCAN I2).eval ((Cmd.op (.nonEmpty NEF SCAN)).eval u)).get PSIG
        = _ := Cmd.eval_get_of_not_writes _ _ PSIG (by decide)
    rw [hev, Cmd.eval_ifBit_true _ _ _ _ hne, Cmd.eval_seq]
    have hlt := ltCheck_run VAL PSIG I3 (l[i]'hi) M.sig
      (b && (l.take i).all (fun x => decide (x < M.sig))) _
      (by decide) (by decide) (by decide) hval (by rw [hP3]; exact f3)
      (by rw [hF3]; exact f2)
    refine ⟨?_, ?_, ?_⟩
    · rw [Cmd.eval_get_of_not_writes _ _ SCAN (by decide), hscan]
    · rw [hlt, all_take_succ (fun x => decide (x < M.sig)) l i hi, ← Bool.and_assoc]
    · rw [Cmd.eval_get_of_not_writes _ _ PSIG (by decide), hP3]; exact f3
  · -- an idle iteration
    have hlen : l.length ≤ i := Nat.le_of_not_lt hi
    have hd : l.drop i = [] := List.drop_eq_nil_of_le hlen
    have hd1 : l.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have ht : l.take i = l := List.take_of_length_le hlen
    have ht1 : l.take (i + 1) = l := List.take_of_length_le (by omega)
    rw [hd] at e1
    have hne : ((Cmd.op (.nonEmpty NEF SCAN)).eval u).get NEF ≠ [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, e1, encSyms_nil]
      decide
    rw [hev, Cmd.eval_ifBit_false _ _ _ _ hne, hd1, ht1, ← ht]
    exact SInv_frame nop M _ _ _ (by decide) (by decide) (by decide)
      (SInv_frame _ M _ _ u (by decide) (by decide) (by decide) ⟨e1, e2, e3⟩)

theorem sLoop_run (M : flatTM) (l : List Nat) (b : Bool) (s : State)
    (hSREG : s.get SREG = encSyms l)
    (hFLG : s.get FLG = (if b then [1] else []))
    (hPSIG : s.get PSIG = List.replicate M.sig 1) :
    ((sLoop.eval s)).get FLG
      = (if b && l.all (fun x => decide (x < M.sig)) then [1] else []) := by
  have hev : sLoop.eval s
      = (Cmd.forBnd I1 SREG sBody).eval ((Cmd.op (.copy SCAN SREG)).eval s) := by
    unfold sLoop; rw [Cmd.eval_seq]
  set u := (Cmd.op (.copy SCAN SREG)).eval s with hu
  have hu0 : SInv M l b u := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hu, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hSREG
    · rw [hu, Cmd.eval_op]
      simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (FLG : Var) ≠ SCAN)]
      exact hFLG
    · rw [hu, Cmd.eval_op]
      simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (PSIG : Var) ≠ SCAN)]
      exact hPSIG
  have hbnd : u.get SREG = encSyms l := by
    rw [hu, Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (SREG : Var) ≠ SCAN)]
    exact hSREG
  have hge : l.length ≤ (encSyms l).length := encSyms_length_ge l
  rw [hev, Cmd.eval_forBnd, hbnd]
  have key := Cmd.foldlState_range_induct sBody I1 (encSyms l).length u
    (fun i t => SInv M (l.drop i) (b && (l.take i).all (fun x => decide (x < M.sig))) t)
    (by simpa using hu0)
    (fun i t _ hM => sBody_step M l b i t hM)
  obtain ⟨-, hF, -⟩ := key
  rw [hF, List.take_of_length_le hge]


/-! ### Stage G, assembled -/

/-- Stage P's outputs, as stage G reads them. -/
def PVals (M : flatTM) (str : List Nat) (s : State) : Prop :=
  s.get PSIG = List.replicate M.sig 1
  ∧ s.get PTAPES = List.replicate M.tapes 1
  ∧ s.get PSTATES = List.replicate M.states 1
  ∧ s.get PSTART = List.replicate M.start 1
  ∧ s.get PNHALT = List.replicate M.halt.length 1
  ∧ s.get PNTRANS = List.replicate M.trans.length 1
  ∧ s.get PTRANS = encSyms (transFlat M)
  ∧ s.get SREG = encSyms str

private theorem PVals_frame (c : Cmd) (M : flatTM) (str : List Nat) (s : State)
    (h1 : PSIG ∉ c.writes) (h2 : PTAPES ∉ c.writes) (h3 : PSTATES ∉ c.writes)
    (h4 : PSTART ∉ c.writes) (h5 : PNHALT ∉ c.writes) (h6 : PNTRANS ∉ c.writes)
    (h7 : PTRANS ∉ c.writes) (h8 : SREG ∉ c.writes)
    (h : PVals M str s) : PVals M str (c.eval s) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
  exact ⟨by rw [Cmd.eval_get_of_not_writes c s _ h1]; exact e1,
    by rw [Cmd.eval_get_of_not_writes c s _ h2]; exact e2,
    by rw [Cmd.eval_get_of_not_writes c s _ h3]; exact e3,
    by rw [Cmd.eval_get_of_not_writes c s _ h4]; exact e4,
    by rw [Cmd.eval_get_of_not_writes c s _ h5]; exact e5,
    by rw [Cmd.eval_get_of_not_writes c s _ h6]; exact e6,
    by rw [Cmd.eval_get_of_not_writes c s _ h7]; exact e7,
    by rw [Cmd.eval_get_of_not_writes c s _ h8]; exact e8⟩

def gSuf7 : Cmd := Cmd.op (.clear ZERO)
def gSuf6 : Cmd := sLoop ;; gSuf7
def gSuf5 : Cmd := entryLoop ;; gSuf6
def gSuf4 : Cmd := Cmd.op (.copy TSCAN PTRANS) ;; gSuf5
def gSuf3 : Cmd := eqCheck PTAPES ONE ;; gSuf4
def gSuf2 : Cmd := Cmd.op (.clear ONE) ;; Cmd.op (.appendOne ONE) ;; gSuf3
def gSuf1 : Cmd := eqCheck PNHALT PSTATES ;; gSuf2
def gSuf0 : Cmd := ltCheck PSTART PSTATES I1 ;; gSuf1

/-- **Stage G.** -/
def stageG : Cmd := Cmd.op (.clear FLG) ;; Cmd.op (.appendOne FLG) ;; gSuf0

/-! ### The `Bool` bridge to `S1Map.s1GuardB`

The stream fixes the *order* in which the seven per-entry conjuncts can be
checked; `isValidFlatTM` uses another. `&&` is associative-commutative, so the
two agree — but only after an explicit reassociation. -/

theorem entryPB_eq (M : flatTM) (e : FlatTMTransEntry) :
    entryPB M e
      = (decide (e.src_state < M.states) && decide (e.dst_state < M.states) &&
          decide (e.src_tape_vals.length = M.tapes) &&
          decide (e.dst_write_vals.length = M.tapes) &&
          decide (e.move_dirs.length = M.tapes) &&
          e.src_tape_vals.all (isSomeNatBelow M.sig) &&
          e.dst_write_vals.all (isSomeNatBelow M.sig)) := by
  unfold entryPB
  simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem isValidFlatTM_eq (M : flatTM) :
    isValidFlatTM M
      = (decide (M.start < M.states) && decide (M.halt.length = M.states)
          && M.trans.all (entryPB M)) := by
  unfold isValidFlatTM
  congr 1
  congr 1
  funext e
  exact (entryPB_eq M e).symm

theorem s1GuardB_eq (M : flatTM) (str : List Nat) :
    S1Map.s1GuardB M str
      = (true && decide (M.start < M.states) && decide (M.halt.length = M.states)
          && decide (M.tapes = 1) && M.trans.all (entryPB M)
          && str.all (fun x => decide (x < M.sig))) := by
  unfold S1Map.s1GuardB
  rw [isValidFlatTM_eq]
  simp only [Bool.true_and, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-! ### Stage G's run lemma -/

private theorem stageG_eval (s : State) :
    stageG.eval s
      = gSuf0.eval ((Cmd.op (.appendOne FLG)).eval ((Cmd.op (.clear FLG)).eval s)) := by
  unfold stageG; rw [Cmd.eval_seq, Cmd.eval_seq]

/-- **Stage G is correct**: the flag register ends up holding exactly
`S1Map.s1GuardB M str`, and register `0` ends empty. Like stage P, no validity
hypothesis. -/
theorem stageG_run (M : flatTM) (str : List Nat) (s : State) (hP : PVals M str s) :
    (stageG.eval s).get FLG = (if S1Map.s1GuardB M str then [1] else [])
    ∧ (stageG.eval s).get ZERO = [] := by
  -- FLG := [1]
  have hw2F : ((Cmd.op (.appendOne FLG)).eval ((Cmd.op (.clear FLG)).eval s)).get FLG
      = (if true then [1] else []) := by
    rw [Cmd.eval_op, Cmd.eval_op]
    simp [Op.eval, State.get_set_eq]
  have hw2P : PVals M str ((Cmd.op (.appendOne FLG)).eval ((Cmd.op (.clear FLG)).eval s)) :=
    PVals_frame _ M str _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (PVals_frame _ M str s (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hP)
  set w2 := (Cmd.op (.appendOne FLG)).eval ((Cmd.op (.clear FLG)).eval s) with hw2
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hw2P
  -- start < states
  have hw3F := ltCheck_run PSTART PSTATES I1 M.start M.states true w2
    (by decide) (by decide) (by decide) p4 p3 hw2F
  have hw3P := PVals_frame (ltCheck PSTART PSTATES I1) M str w2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩
  set w3 := (ltCheck PSTART PSTATES I1).eval w2 with hw3
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hw3P
  -- |halt| = states
  have hw4F := eqCheck_run PNHALT PSTATES M.halt.length M.states _ w3 q5 q3 hw3F
  have hw4P := PVals_frame (eqCheck PNHALT PSTATES) M str w3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩
  set w4 := (eqCheck PNHALT PSTATES).eval w3 with hw4
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hw4P
  -- ONE := [1]
  have hw6O : ((Cmd.op (.appendOne ONE)).eval ((Cmd.op (.clear ONE)).eval w4)).get ONE
      = List.replicate 1 1 := by
    rw [Cmd.eval_op, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append]
    rfl
  have hw6F : ((Cmd.op (.appendOne ONE)).eval ((Cmd.op (.clear ONE)).eval w4)).get FLG
      = w4.get FLG := by
    rw [Cmd.eval_get_of_not_writes _ _ FLG (by decide),
      Cmd.eval_get_of_not_writes _ _ FLG (by decide)]
  have hw6P := PVals_frame (Cmd.op (.appendOne ONE)) M str _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (PVals_frame (Cmd.op (.clear ONE)) M str w4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩)
  set w6 := (Cmd.op (.appendOne ONE)).eval ((Cmd.op (.clear ONE)).eval w4) with hw6
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := hw6P
  -- tapes = 1
  have hw7F := eqCheck_run PTAPES ONE M.tapes 1 _ w6 t2 hw6O (by rw [hw6F]; exact hw4F)
  have hw7P := PVals_frame (eqCheck PTAPES ONE) M str w6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩
  set w7 := (eqCheck PTAPES ONE).eval w6 with hw7
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := hw7P
  -- TSCAN := the transition sub-stream
  have hw8T : ((Cmd.op (.copy TSCAN PTRANS)).eval w7).get TSCAN = encSyms (transFlat M) := by
    rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact u7
  have hw8P := PVals_frame (Cmd.op (.copy TSCAN PTRANS)) M str w7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩
  have hw8F : ((Cmd.op (.copy TSCAN PTRANS)).eval w7).get FLG = w7.get FLG :=
    Cmd.eval_get_of_not_writes _ _ FLG (by decide)
  set w8 := (Cmd.op (.copy TSCAN PTRANS)).eval w7 with hw8
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hw8P
  -- the transition-table loop
  have hEInv : EInv M (transFlat M) _ w8 := ⟨hw8T, by rw [hw8F]; exact hw7F, v1, v3, v2⟩
  have hw9 := entryLoop_run M _ w8 (by rw [v6, List.length_replicate]) hEInv
  have hw9P := PVals_frame entryLoop M str w8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩
  set w9 := entryLoop.eval w8 with hw9d
  obtain ⟨-, hw9F, hw9S, -, -⟩ := hw9
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hw9P
  -- the input-string loop
  have hw10F := sLoop_run M str _ w9 z8 hw9F hw9S
  set w10 := sLoop.eval w9 with hw10d
  -- the final `clear ZERO`
  have hchain : stageG.eval s = (Cmd.op (.clear ZERO)).eval w10 := by
    rw [stageG_eval, ← hw2]
    show gSuf0.eval w2 = _
    unfold gSuf0; rw [Cmd.eval_seq, ← hw3]
    unfold gSuf1; rw [Cmd.eval_seq, ← hw4]
    unfold gSuf2; rw [Cmd.eval_seq, Cmd.eval_seq, ← hw6]
    unfold gSuf3; rw [Cmd.eval_seq, ← hw7]
    unfold gSuf4; rw [Cmd.eval_seq, ← hw8]
    unfold gSuf5; rw [Cmd.eval_seq, ← hw9d]
    unfold gSuf6; rw [Cmd.eval_seq, ← hw10d]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hchain, Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ (by decide : (FLG : Var) ≠ ZERO)]
    rw [hw10F, s1GuardB_eq]
  · rw [hchain, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq]

/-! ## The two stages, composed -/

/-- **Stages P and G together.** -/
def stagePG : Cmd := stageP ;; stageG

/-- **The parse/guard front end is correct.** From the frozen head layout's
machine and input-string registers, `stagePG` materialises every machine
parameter in the scratch frame and decides `S1Map.s1GuardB` into `FLG`. -/
theorem stagePG_run (M : flatTM) (str : List Nat) (s : State)
    (hM : s.get MREG = encSyms (flattenTM M))
    (hS : s.get SREG = encSyms str) :
    (stagePG.eval s).get FLG = (if S1Map.s1GuardB M str then [1] else [])
    ∧ (stagePG.eval s).get ZERO = []
    ∧ (stagePG.eval s).get PSIG = List.replicate M.sig 1
    ∧ (stagePG.eval s).get PTAPES = List.replicate M.tapes 1
    ∧ (stagePG.eval s).get PSTATES = List.replicate M.states 1
    ∧ (stagePG.eval s).get PSTART = List.replicate M.start 1
    ∧ (stagePG.eval s).get PNHALT = List.replicate M.halt.length 1
    ∧ (stagePG.eval s).get PHALT = M.halt.map bitOf
    ∧ (stagePG.eval s).get PNTRANS = List.replicate M.trans.length 1
    ∧ (stagePG.eval s).get PTRANS = encSyms (transFlat M) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := stageP_run M s hM
  have hSREG : (stageP.eval s).get SREG = encSyms str := by
    rw [Cmd.eval_get_of_not_writes stageP s SREG (by decide)]; exact hS
  have hev : stagePG.eval s = stageG.eval (stageP.eval s) := by
    unfold stagePG; rw [Cmd.eval_seq]
  obtain ⟨hF, hZ⟩ := stageG_run M str (stageP.eval s)
    ⟨a1, a2, a3, a4, a5, a7, a8, hSREG⟩
  refine ⟨by rw [hev]; exact hF, by rw [hev]; exact hZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PSIG (by decide)]; exact a1
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PTAPES (by decide)]; exact a2
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PSTATES (by decide)]; exact a3
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PSTART (by decide)]; exact a4
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PNHALT (by decide)]; exact a5
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PHALT (by decide)]; exact a6
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PNTRANS (by decide)]; exact a7
  · rw [hev, Cmd.eval_get_of_not_writes stageG _ PTRANS (by decide)]; exact a8


/-! ## The frame

`s1RegBound = 48`; P + G fit in `32`, leaving `[32, 48)` for stages Σ / I / C /
F / M. Register `0` (`ZERO`) is written but ends `[]` (`stageG_run`), which is
what the fourth seam's scrub needs. -/

/-- **P + G touch only registers `< 32`** — the `usesBelow` ingredient for
`S1Witness.s1_reductionLang`, and the budget every later stage must respect. -/
theorem stagePG_usesBelow : Cmd.UsesBelow stagePG 32 := by
  simp [stagePG, stageP, pSuf1, pSuf2, pSuf3, pSuf4, pSuf5, pSuf6, pSuf7, pSuf8,
    pSuf9, haltBody, readItem, stageG, gSuf0, gSuf1, gSuf2, gSuf3, gSuf4, gSuf5,
    gSuf6, gSuf7, entryLoop, entryBody, eSuf2, eSuf3, eSuf4, fieldCheck,
    arityOptCheck, arityMoveCheck, optLoop, skipLoop, optCheck, sLoop, sBody,
    ltCheck, eqCheck, andIn, nop, CliqueRelTM.readNum, CliqueRelTM.cSkip,
    CliqueRelTM.ltBit, Cmd.UsesBelow, Op.UsesBelow,
    ZERO, MREG, SREG, PSIG, PTAPES, PSTATES, PSTART, PNHALT, PHALT, PNTRANS,
    PTRANS, SCAN, FLG, VAL, RES, ONE, TSCAN, NEF, I1, I2, I3, I4, I5,
    CliqueRelTM.HEAD, CliqueRelTM.INBLK, CliqueRelTM.SKIPR, CliqueRelTM.LT_B]

theorem stagePG_usesBelow_48 : Cmd.UsesBelow stagePG 48 :=
  Cmd.UsesBelow_mono (by omega) stagePG_usesBelow


/-- **P + G leave the head layout's interface registers alone.** Registers `1`
(machine) and `2` (input string) are only ever *copied* into scratch cursors,
and `3`/`4`/`5` are never mentioned — so stages Σ / I / C / F still see
`1^maxSize` and `1^steps` where C8-4 put them, and stage M finds `1`–`5` free
to overwrite. -/
theorem stagePG_frame (s : State) (r : Var)
    (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) :
    (stagePG.eval s).get r = s.get r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Cmd.eval_get_of_not_writes stagePG s 1 (by decide)
  · exact Cmd.eval_get_of_not_writes stagePG s 2 (by decide)
  · exact Cmd.eval_get_of_not_writes stagePG s 3 (by decide)
  · exact Cmd.eval_get_of_not_writes stagePG s 4 (by decide)
  · exact Cmd.eval_get_of_not_writes stagePG s 5 (by decide)

end S1Parse
