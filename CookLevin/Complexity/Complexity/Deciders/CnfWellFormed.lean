import Complexity.Complexity.Deciders.CnfSerialize

set_option autoImplicit false

/-! # Which bit strings ARE CNFs — a finite-state characterisation

The pure half of bottom-up item 2 (`SATStr`: SAT as a *string* language).

To present SAT as a language over `List Bool` we need to say, of a raw bit
string, whether it *is* the canonical encoding of a CNF — and a machine has to
be able to check it. This file answers both at once:

```
scanStep : Bool × Bool × Nat → Nat → Bool × Bool × Nat
```

is a **four-state DFA with a counter**, run left to right over the cell stream.
Its state is `(inLit, pending)`:

| state | meaning | on cell `1` | on cell `≠ 1` |
|---|---|---|---|
| `(false, _)` | at a literal slot | `(true, false)` — a literal starts | `(false, false)`, **count += 1** — clause end |
| `(true, false)` | reading the polarity bit | `(true, true)` | `(true, true)` |
| `(true, true)` | inside the unary variable block | `(true, true)` | `(false, true)` — literal end |

and the two results are

* `wfCnfB_iff` — over `0`/`1` streams, `wfCnfB l = true` **iff** `l` is
  `encodeCnf N` for some `N`. The accepting state is `(false, false)`: at a
  literal slot *and* with no clause left open. The `pending` bit is what a naive
  three-state version lacks, and without it `[1,1,0]` (a literal with no
  clause terminator) would validate — see `not_wfCnfB_lit_unterminated`.
* `cnfCount_eq_length` — the same left-to-right pass counts the clauses, which
  is the one derived field (`CLAUSE_TALLY = 1^|N|`) the SAT verifier's register
  layout needs and the raw stream does not carry.

`parseTotal` closes the loop: a **total** decode `List Nat → cnf`, the existing
parser `CnfSerialize.decCnf` on the validating streams and the unsatisfiable
one-empty-clause CNF `[[]]` on everything else. So "this string is not an
encoding" and "this string encodes an unsatisfiable formula" are the same
verdict, which is what lets one machine decide both.

⚠ Every statement about `l` being an encoding carries `∀ v ∈ l, v ≤ 1`. That is
not a technicality: `scanStep` reads any cell `≠ 1` as a `0`, exactly as the
machine's `ifBit` does, so on a stream with a `2` in it the scanner and the
grammar genuinely disagree. Bit strings (`certState`) never produce such a cell.

Probe: `probes/SATStrProbe.lean` §1/§2 (exhaustive over every `0`/`1` stream of
length `≤ 8`, against `decCnf`).
-/

namespace CnfWellFormed

open EvalCnfCmd (encodeLit encodeClause encodeCnf)
open CnfSerialize (clauseBody)

/-! ## The scanner -/

/-- One cell of the scan: the DFA state `(inLit, pending)` plus the clause
counter. See the table in the module docstring. -/
def scanStep : Bool × Bool × Nat → Nat → Bool × Bool × Nat
  | (false, _, k), cell => if cell = 1 then (true, false, k) else (false, false, k + 1)
  | (true, false, k), _ => (true, true, k)
  | (true, true, k), cell => if cell = 1 then (true, true, k) else (false, true, k)

/-- The scan of a whole stream, from the initial state. -/
def scanRun (l : List Nat) : Bool × Bool × Nat := l.foldl scanStep (false, false, 0)

/-- **Well-formedness**: the scan ends at a literal slot with no clause open.
Written as the machine tests it — two flag registers, both empty. -/
def wfCnfB (l : List Nat) : Bool := !(scanRun l).1 && !(scanRun l).2.1

/-- The clause count the same pass produces. -/
def cnfCount (l : List Nat) : Nat := (scanRun l).2.2

/-- **The total decode.** A validating stream decodes by the canonical parser;
everything else decodes to `[[]]`, the one-empty-clause CNF, which is
unsatisfiable (`not_sat_botCnf`). -/
def parseTotal (l : List Nat) : cnf :=
  if wfCnfB l then (CnfSerialize.decCnf l).getD [[]] else [[]]

/-- The junk value, named: one empty clause. -/
def botCnf : cnf := [[]]

theorem encodeCnf_botCnf : encodeCnf botCnf = [0] := rfl

theorem botCnf_length : botCnf.length = 1 := rfl

/-- `[[]]` is unsatisfiable: an empty clause has no satisfying literal. -/
theorem not_sat_botCnf : ¬ SAT botCnf := by
  rintro ⟨a, ha⟩
  exact absurd ha (by simp [botCnf, satisfiesCnf, evalCnf, evalClause])

/-! ## The scanner accepts every encoding, and counts its clauses

Bottom-up through the grammar: one literal, one clause, then the CNF. The
counter is carried as a parameter throughout — no step of the scan reads it, so
every lemma is stated at an arbitrary `k`. -/

theorem scanRun_append (l₁ l₂ : List Nat) (p : Bool × Bool × Nat) :
    (l₁ ++ l₂).foldl scanStep p = l₂.foldl scanStep (l₁.foldl scanStep p) :=
  List.foldl_append

/-- Inside a unary variable block: `1`s do not move the scanner. -/
theorem scan_replicate_one (v k : Nat) :
    (List.replicate v 1).foldl scanStep (true, true, k) = (true, true, k) := by
  induction v with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      show (List.replicate n 1).foldl scanStep (scanStep (true, true, k) 1) = _
      rw [show scanStep (true, true, k) 1 = (true, true, k) from rfl]
      exact ih

/-- One literal block takes the scanner from a literal slot to "literal read,
clause pending", leaving the counter alone. -/
theorem scan_encodeLit (l : literal) (p : Bool) (k : Nat) :
    (encodeLit l).foldl scanStep (false, p, k) = (false, true, k) := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).foldl scanStep (false, p, k)
      = (false, true, k)
  show (List.replicate v 1 ++ [0]).foldl scanStep
      (scanStep (scanStep (false, p, k) 1) (if pol then 1 else 0)) = (false, true, k)
  have h1 : scanStep (false, p, k) 1 = (true, false, k) := rfl
  rw [h1]
  have h2 : scanStep (true, false, k) (if pol then 1 else 0) = (true, true, k) := by
    cases pol <;> rfl
  rw [h2, scanRun_append, scan_replicate_one]
  rfl

/-- A clause's literal run leaves the scanner at a literal slot. -/
theorem scan_clauseBody (C : clause) (p : Bool) (k : Nat) :
    ∃ q, (clauseBody C).foldl scanStep (false, p, k) = (false, q, k) := by
  induction C generalizing p with
  | nil => exact ⟨p, rfl⟩
  | cons l C ih =>
      rw [CnfSerialize.clauseBody_cons, scanRun_append, scan_encodeLit l p k]
      exact ih true

/-- One encoded clause returns the scanner to the accepting state and bumps the
counter by exactly one. -/
theorem scan_encodeClause (C : clause) (p : Bool) (k : Nat) :
    (encodeClause C).foldl scanStep (false, p, k) = (false, false, k + 1) := by
  obtain ⟨q, hq⟩ := scan_clauseBody C p k
  rw [CnfSerialize.encodeClause_eq, scanRun_append, hq]
  rfl

/-- **The scanner accepts every encoding**, and its counter is the clause
count. -/
theorem scan_encodeCnf (N : cnf) (k : Nat) :
    (encodeCnf N).foldl scanStep (false, false, k) = (false, false, k + N.length) := by
  induction N generalizing k with
  | nil => rfl
  | cons C N ih =>
      rw [CnfSerialize.encodeCnf_cons, scanRun_append, scan_encodeClause C false k, ih (k + 1)]
      show (false, false, k + 1 + N.length) = (false, false, k + (N.length + 1))
      rw [Nat.add_assoc, Nat.add_comm 1 N.length]

theorem scanRun_encodeCnf (N : cnf) : scanRun (encodeCnf N) = (false, false, N.length) := by
  show (encodeCnf N).foldl scanStep (false, false, 0) = _
  rw [scan_encodeCnf N 0, Nat.zero_add]

theorem wfCnfB_encodeCnf (N : cnf) : wfCnfB (encodeCnf N) = true := by
  simp [wfCnfB, scanRun_encodeCnf]

theorem cnfCount_encodeCnf (N : cnf) : cnfCount (encodeCnf N) = N.length := by
  simp [cnfCount, scanRun_encodeCnf]

/-! ## …and nothing else: an accepted stream IS an encoding

The converse, by strong induction on the stream's length. The two halves have to
be proven together: from the accepting state a stream is a whole CNF, and from
`(false, true)` — a clause is open — it is "the rest of a clause, then a CNF".
The states `(false, false)` and `(false, true)` have the *same* transitions and
differ only in acceptance, which is exactly why one induction serves both. -/

/-- The unary block, read backwards: from inside a variable block the scanner
can only reach a literal slot by finishing the block with a `0`. -/
theorem replicate_of_scan_inVar :
    ∀ (u : List Nat), (∀ v ∈ u, v ≤ 1) → ∀ (k : Nat),
      ((u.foldl scanStep (true, true, k)).1 = false ∧
        (u.foldl scanStep (true, true, k)).2.1 = false) →
      ∃ (v : Nat) (w : List Nat), u = List.replicate v 1 ++ 0 :: w ∧ w.length < u.length ∧
        (w.foldl scanStep (false, true, k)).1 = false ∧
        (w.foldl scanStep (false, true, k)).2.1 = false
  | [], _, _, h => absurd h.1 (by simp)
  | a :: u, hbit, k, h => by
      have ha : a ≤ 1 := hbit a (by simp)
      have hbit' : ∀ v ∈ u, v ≤ 1 := fun v hv => hbit v (by simp [hv])
      rcases Nat.lt_or_ge a 1 with hlt | hge
      · -- `a = 0`: the block ends here
        have ha0 : a = 0 := by omega
        subst ha0
        have hstep : scanStep (true, true, k) 0 = (false, true, k) := rfl
        rw [List.foldl_cons, hstep] at h
        exact ⟨0, u, rfl, by simp, h.1, h.2⟩
      · -- `a = 1`: still inside the block
        have ha1 : a = 1 := by omega
        subst ha1
        have hstep : scanStep (true, true, k) 1 = (true, true, k) := rfl
        rw [List.foldl_cons, hstep] at h
        obtain ⟨v, w, hw, hlen, h1, h2⟩ := replicate_of_scan_inVar u hbit' k h
        refine ⟨v + 1, w, ?_, ?_, h1, h2⟩
        · rw [List.replicate_succ, List.cons_append, ← hw]
        · simp only [List.length_cons]; omega

/-- **The converse.** Both halves at once, by strong induction on the fuel `n`. -/
theorem encoding_of_scan :
    ∀ (n : Nat) (l : List Nat), l.length ≤ n → (∀ v ∈ l, v ≤ 1) → ∀ k : Nat,
      ((l.foldl scanStep (false, false, k)).1 = false ∧
          (l.foldl scanStep (false, false, k)).2.1 = false →
        ∃ N : cnf, encodeCnf N = l) ∧
      ((l.foldl scanStep (false, true, k)).1 = false ∧
          (l.foldl scanStep (false, true, k)).2.1 = false →
        ∃ (C : clause) (N : cnf), clauseBody C ++ 0 :: encodeCnf N = l) := by
  intro n
  induction n with
  | zero =>
      intro l hl _ _
      have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_antisymm hl (Nat.zero_le _))
      subst hnil
      exact ⟨fun _ => ⟨[], rfl⟩, fun h => absurd h.2 (by simp)⟩
  | succ n ih =>
      intro l hl hbit k
      cases l with
      | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun h => absurd h.2 (by simp)⟩
      | cons a t =>
          have ha : a ≤ 1 := hbit a (by simp)
          have hbitT : ∀ v ∈ t, v ≤ 1 := fun v hv => hbit v (by simp [hv])
          rcases Nat.lt_or_ge a 1 with hlt | hge
          · -- `a = 0`: a clause terminator; the rest is a CNF
            have ha0 : a = 0 := by omega
            subst ha0
            have hstep : ∀ p : Bool, scanStep (false, p, k) 0 = (false, false, k + 1) :=
              fun _ => rfl
            have hT : t.length ≤ n := by simp only [List.length_cons] at hl; omega
            have key : (t.foldl scanStep (false, false, k + 1)).1 = false ∧
                (t.foldl scanStep (false, false, k + 1)).2.1 = false →
                ∃ N : cnf, encodeCnf N = t := (ih t hT hbitT (k + 1)).1
            constructor
            · intro h
              rw [List.foldl_cons, hstep] at h
              obtain ⟨N, hN⟩ := key h
              exact ⟨[] :: N, by rw [CnfSerialize.encodeCnf_cons, hN]; rfl⟩
            · intro h
              rw [List.foldl_cons, hstep] at h
              obtain ⟨N, hN⟩ := key h
              exact ⟨[], N, by rw [hN]; rfl⟩
          · -- `a = 1`: a literal starts
            have ha1 : a = 1 := by omega
            subst ha1
            have main : ∀ p : Bool,
                ((1 :: t).foldl scanStep (false, p, k)).1 = false ∧
                  ((1 :: t).foldl scanStep (false, p, k)).2.1 = false →
                ∃ (C : clause) (N : cnf), clauseBody C ++ 0 :: encodeCnf N = 1 :: t := by
              intro p h
              have hstep : scanStep (false, p, k) 1 = (true, false, k) := rfl
              rw [List.foldl_cons, hstep] at h
              cases t with
              | nil => exact absurd h.1 (by simp)
              | cons pb u =>
                  have hbitU : ∀ v ∈ u, v ≤ 1 := fun v hv => hbitT v (by simp [hv])
                  have hstep2 : scanStep (true, false, k) pb = (true, true, k) := rfl
                  rw [List.foldl_cons, hstep2] at h
                  obtain ⟨v, w, hw, hlenw, hw1, hw2⟩ := replicate_of_scan_inVar u hbitU k h
                  have hbitW : ∀ z ∈ w, z ≤ 1 := fun z hz => hbitU z (by rw [hw]; simp [hz])
                  have hlen : w.length ≤ n := by
                    simp only [List.length_cons] at hl
                    omega
                  obtain ⟨C, N, hCN⟩ := (ih w hlen hbitW k).2 ⟨hw1, hw2⟩
                  refine ⟨(decide (pb = 1), v) :: C, N, ?_⟩
                  have hpb : pb ≤ 1 := hbitT pb (by simp)
                  have hpol : (if decide (pb = 1) then (1 : Nat) else 0) = pb := by
                    rcases Nat.lt_or_ge pb 1 with h' | h'
                    · have : pb = 0 := by omega
                      subst this; rfl
                    · have : pb = 1 := by omega
                      subst this; rfl
                  rw [CnfSerialize.clauseBody_cons]
                  show (1 :: (if decide (pb = 1) then (1 : Nat) else 0) ::
                      (List.replicate v 1 ++ [0])) ++ clauseBody C ++ 0 :: encodeCnf N
                    = 1 :: pb :: u
                  rw [hpol, hw, ← hCN]
                  simp [List.append_assoc]
            refine ⟨fun h => ?_, fun h => main true h⟩
            obtain ⟨C, N, hCN⟩ := main false h
            exact ⟨C :: N, by
              rw [CnfSerialize.encodeCnf_cons, CnfSerialize.encodeClause_eq, List.append_assoc]
              exact hCN⟩

/-- **The characterisation.** Over `0`/`1` streams the scanner accepts exactly
the canonical CNF encodings. -/
theorem wfCnfB_iff (l : List Nat) (hbit : ∀ v ∈ l, v ≤ 1) :
    wfCnfB l = true ↔ ∃ N : cnf, encodeCnf N = l := by
  constructor
  · intro h
    have h' : (scanRun l).1 = false ∧ (scanRun l).2.1 = false := by
      simp only [wfCnfB, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h
    exact (encoding_of_scan l.length l (Nat.le_refl _) hbit 0).1 h'
  · rintro ⟨N, rfl⟩
    exact wfCnfB_encodeCnf N

/-! ## `parseTotal` — the decode that never fails -/

theorem parseTotal_encodeCnf (N : cnf) : parseTotal (encodeCnf N) = N := by
  simp only [parseTotal]
  rw [if_pos (wfCnfB_encodeCnf N), CnfSerialize.decCnf_encodeCnf N]
  rfl

/-- On a validating stream, `parseTotal` recovers *the* CNF: the parser
`CnfSerialize.decCnf` is a left inverse of `encodeCnf`, so it is exact wherever
the scanner says the stream is an encoding. -/
theorem encodeCnf_parseTotal (l : List Nat) (hbit : ∀ v ∈ l, v ≤ 1)
    (hwf : wfCnfB l = true) : encodeCnf (parseTotal l) = l := by
  obtain ⟨N, hN⟩ := (wfCnfB_iff l hbit).mp hwf
  rw [← hN, parseTotal_encodeCnf N]

/-- Off the image the decode is the junk CNF — by definition, not by accident:
this is what makes "not an encoding" and "unsatisfiable" the same verdict. -/
theorem parseTotal_of_not_wf (l : List Nat) (hwf : wfCnfB l = false) :
    parseTotal l = botCnf := by
  simp only [parseTotal, hwf, Bool.false_eq_true, if_false]
  rfl

/-- **The clause counter is the clause count**, on the streams where it is
used. -/
theorem cnfCount_eq_length (l : List Nat) (hbit : ∀ v ∈ l, v ≤ 1)
    (hwf : wfCnfB l = true) : cnfCount l = (parseTotal l).length := by
  conv_lhs => rw [← encodeCnf_parseTotal l hbit hwf]
  exact cnfCount_encodeCnf _

/-! ## The `pending` bit is load-bearing

Without it the scanner would accept a literal run with no clause terminator,
which is not an encoding of anything. -/

theorem not_wfCnfB_lit_unterminated : wfCnfB [1, 1, 0] = false := by decide

theorem not_wfCnfB_bare_one : wfCnfB [1] = false := by decide

theorem wfCnfB_empty : wfCnfB [] = true := by decide

theorem wfCnfB_zero : wfCnfB [0] = true := by decide

end CnfWellFormed
