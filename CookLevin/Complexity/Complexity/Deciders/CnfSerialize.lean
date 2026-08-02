import Complexity.Complexity.Deciders.EvalCnfCmd
import Complexity.Lang.Serialize

set_option autoImplicit false

/-! # `Serialize cnf` — the canonical CNF layout, with a real parser

The **tail end** of the honesty surface (FINDING AK): the endpoint witness's
`decodeOut` is `FSATSATFree.decodeOut`, and until now it was

```lean
noncomputable def decodeOut (s : State) : cnf :=
  Function.invFun encodeCnf (State.get s CNFOUT)
```

`Function.invFun` is classical, noncomputable, and *unconstrained off the image*
of `encodeCnf` — the reader has to check that the junk branch cannot be used to
smuggle in an answer. This module replaces it with a **parser**: `decCnf` walks
the bit stream by the same grammar `encodeCnf` writes, and `decCnf_encodeCnf`
proves it is a genuine left inverse (no `Classical.choice`).

The grammar (`EvalCnfCmd`'s header, restated as the parser reads it):

```
literal  ::= 1 polBit 1^v 0
clause   ::= literal* 0
cnf      ::= clause*            -- runs to the end of the stream
```

`decClause`/`decCnfAux` carry a fuel argument rather than a well-founded
recursion; `decCnf` seeds it with the stream length, which always suffices
because every clause costs at least one cell.

## The four `Serialize` laws for `cnf`

* `dec_enc` — `decCnf_encodeCnf`, below;
* `enc_bit` — `EvalCnfCmd.encodeCnf_bit`, already proven;
* `enc_length_le` — `EvalCnfCmd.encodeCnf_length` (`≤ 5 · size`), already proven;
* `size_le_enc_length` — `size_le_encodeCnf_length`, below. This is the
  **no-compression** half of the sandwich, and it is new. It is what a future
  head-side fix needs (see `Lang/Serialize.lean`): the front program can only
  build `1^(size x)` on-machine if the input register is at least that long.
  ⚠ Since FINDING AT (2026-08-05) the law is stated up to a polynomial
  `sizeLB`; `encodeCnf` satisfies the identity form, so this instance takes
  `sizeLB := id` and the theorem below is unchanged.
-/

namespace CnfSerialize

open Complexity.Lang
open EvalCnfCmd (encodeLit encodeClause encodeCnf)

/-! ## The parser -/

/-- Read one unary block `1^v 0` off the front of the stream. -/
def scanUnary : List Nat → Option (Nat × List Nat)
  | [] => none
  | 0 :: rest => some (0, rest)
  | 1 :: rest => (scanUnary rest).map (fun p => (p.1 + 1, p.2))
  | _ :: _ => none

/-- Read one clause: literals `1 pol 1^v 0` until the `0` at a literal slot.
`f` is fuel (an upper bound on the literal count). -/
def decClause : Nat → List Nat → Option (clause × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: rest => some ([], rest)
  | f + 1, 1 :: p :: rest =>
      (scanUnary rest).bind fun vr =>
        (decClause f vr.2).map fun cr => ((decide (p = 1), vr.1) :: cr.1, cr.2)
  | _ + 1, _ => none

/-- Read clauses until the stream is exhausted. `f` is fuel (an upper bound on
the clause count). -/
def decCnfAux : Nat → List Nat → Option cnf
  | _, [] => some []
  | 0, _ => none
  | f + 1, l =>
      (decClause (f + 1) l).bind fun cr => (decCnfAux f cr.2).map fun N => cr.1 :: N

/-- **The CNF parser.** The stream's own length is always enough fuel. -/
def decCnf (l : List Nat) : Option cnf := decCnfAux l.length l

/-! ## `decCnf` inverts `encodeCnf` -/

/-- The literal run of a clause, i.e. `encodeClause C` without its `0`. -/
def clauseBody (C : clause) : List Nat :=
  C.foldr (fun l acc => encodeLit l ++ acc) []

theorem encodeClause_eq (C : clause) : encodeClause C = clauseBody C ++ [0] := rfl

theorem clauseBody_cons (l : literal) (C : clause) :
    clauseBody (l :: C) = encodeLit l ++ clauseBody C := rfl

/-- The unary scanner reads exactly the block it is given. -/
theorem scanUnary_replicate (v : Nat) (rest : List Nat) :
    scanUnary (List.replicate v 1 ++ 0 :: rest) = some (v, rest) := by
  induction v with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      show (scanUnary (List.replicate n 1 ++ 0 :: rest)).map (fun p => (p.1 + 1, p.2))
        = some (n + 1, rest)
      rw [ih]
      rfl

/-- One step of `decClause` at a literal slot. -/
theorem decClause_lit (f p v : Nat) (rest : List Nat) :
    decClause (f + 1) (1 :: p :: (List.replicate v 1 ++ 0 :: rest))
      = (decClause f rest).map (fun cr => ((decide (p = 1), v) :: cr.1, cr.2)) := by
  show (scanUnary (List.replicate v 1 ++ 0 :: rest)).bind
      (fun vr => (decClause f vr.2).map fun cr => ((decide (p = 1), vr.1) :: cr.1, cr.2)) = _
  rw [scanUnary_replicate]
  rfl

/-- **The clause parser is exact**: with enough fuel it reads back the clause
and leaves the rest of the stream untouched. -/
theorem decClause_body (C : clause) :
    ∀ (f : Nat) (tail : List Nat), C.length < f →
      decClause f (clauseBody C ++ 0 :: tail) = some (C, tail) := by
  induction C with
  | nil =>
      intro f tail hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rfl
  | cons l C ih =>
      intro f tail hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rcases l with ⟨pol, v⟩
      have hC : C.length < f' := by
        have : (C.length + 1) < f' + 1 := hf
        omega
      have hsplit : clauseBody ((pol, v) :: C) ++ 0 :: tail
          = 1 :: (if pol then 1 else 0) ::
              (List.replicate v 1 ++ 0 :: (clauseBody C ++ 0 :: tail)) := by
        rw [clauseBody_cons]
        show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0]) ++ clauseBody C)
            ++ 0 :: tail = _
        simp [List.append_assoc]
      rw [hsplit, decClause_lit, ih f' tail hC]
      have hpol : decide ((if pol then 1 else 0) = 1) = pol := by
        cases pol <;> rfl
      rw [hpol]
      rfl

/-- Every clause costs at least one cell per literal, plus its terminator. -/
theorem length_lt_encodeClause (C : clause) : C.length < (encodeClause C).length := by
  rw [encodeClause_eq, List.length_append]
  have h : C.length ≤ (clauseBody C).length := by
    induction C with
    | nil => exact Nat.le_refl 0
    | cons l C ih =>
        rw [clauseBody_cons, List.length_append, List.length_cons]
        have hl : 1 ≤ (encodeLit l).length := by
          rcases l with ⟨pol, v⟩
          show 1 ≤ (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).length
          simp
        omega
  simp only [List.length_singleton]
  omega

theorem encodeCnf_cons (C : clause) (N : cnf) :
    encodeCnf (C :: N) = encodeClause C ++ encodeCnf N := rfl

/-- One `decCnfAux` step on a non-empty stream. -/
theorem decCnfAux_cons (f a : Nat) (t : List Nat) :
    decCnfAux (f + 1) (a :: t)
      = (decClause (f + 1) (a :: t)).bind
          (fun cr => (decCnfAux f cr.2).map fun N => cr.1 :: N) := rfl

/-- **The CNF parser is exact**, given enough fuel. -/
theorem decCnfAux_encodeCnf (N : cnf) :
    ∀ f : Nat, (encodeCnf N).length ≤ f → decCnfAux f (encodeCnf N) = some N := by
  induction N with
  | nil => intro f _; cases f <;> rfl
  | cons C N ih =>
      intro f hf
      have hlen : (encodeCnf (C :: N)).length
          = (encodeClause C).length + (encodeCnf N).length := by
        rw [encodeCnf_cons, List.length_append]
      have hCpos : C.length < (encodeClause C).length := length_lt_encodeClause C
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hCf : C.length < f' + 1 := by omega
      have hNf : (encodeCnf N).length ≤ f' := by omega
      have hstream : encodeCnf (C :: N) = clauseBody C ++ 0 :: encodeCnf N := by
        rw [encodeCnf_cons, encodeClause_eq, List.append_assoc]
        rfl
      obtain ⟨a, t, hat⟩ : ∃ a t, encodeCnf (C :: N) = a :: t := by
        rw [hstream]
        cases hb : clauseBody C with
        | nil => exact ⟨0, encodeCnf N, rfl⟩
        | cons b bt => exact ⟨b, bt ++ 0 :: encodeCnf N, rfl⟩
      rw [hat, decCnfAux_cons, ← hat, hstream,
        decClause_body C (f' + 1) (encodeCnf N) hCf]
      show (decCnfAux f' (encodeCnf N)).map (fun N' => C :: N') = _
      rw [ih f' hNf]
      rfl

/-- **`decCnf` is a genuine left inverse of `encodeCnf`** — no `Classical`. -/
theorem decCnf_encodeCnf (N : cnf) : decCnf (encodeCnf N) = some N :=
  decCnfAux_encodeCnf N (encodeCnf N).length (Nat.le_refl _)

/-! ## No compression: `encodable.size N ≤ |encodeCnf N|`

The direction the *head* of the chain needs and the one nothing in the
development had: `encodeCnf` never shrinks its input below the type's own size
measure. (`EvalCnfCmd.encodeCnf_length` is the other half, `≤ 5 · size`.) -/

private theorem foldl_encsize_acc {α : Type} [encodable α] :
    ∀ (acc : Nat) (xs : List α),
      xs.foldl (fun a x => a + encodable.size x + 1) acc
        = acc + xs.foldr (fun x s => encodable.size x + 1 + s) 0
  | acc, [] => by simp
  | acc, x :: xs => by
      simp only [List.foldl_cons, List.foldr_cons]
      rw [foldl_encsize_acc (acc + encodable.size x + 1) xs]; omega

private theorem encsize_list_foldr {α : Type} [encodable α] (xs : List α) :
    encodable.size xs = xs.foldr (fun x s => encodable.size x + 1 + s) 0 := by
  show xs.foldl (fun a x => a + encodable.size x + 1) 0 = _
  rw [foldl_encsize_acc 0 xs]; omega

/-- A clause's size is dominated by its literal run. -/
private theorem size_clause_le_body (C : clause) :
    encodable.size C ≤ (clauseBody C).length := by
  rw [encsize_list_foldr C]
  induction C with
  | nil => exact Nat.le_refl 0
  | cons l C ih =>
      rw [clauseBody_cons, List.length_append, List.foldr_cons]
      have hlit : encodable.size l + 1 ≤ (encodeLit l).length := by
        rcases l with ⟨pol, v⟩
        have hlen : (encodeLit (pol, v)).length = v + 3 := by
          show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).length = v + 3
          simp
        have hsz : encodable.size ((pol, v) : literal)
            = encodable.size pol + encodable.size v + 1 := rfl
        have hpol : encodable.size pol ≤ 1 := by
          cases pol
          · exact Nat.zero_le 1
          · exact Nat.le_refl 1
        have hv : encodable.size v = v := rfl
        rw [hlen, hsz, hv]
        omega
      omega

/-- **No compression.** -/
theorem size_le_encodeCnf_length (N : cnf) :
    encodable.size N ≤ (encodeCnf N).length := by
  rw [encsize_list_foldr N]
  induction N with
  | nil => exact Nat.le_refl 0
  | cons C N ih =>
      rw [encodeCnf_cons, List.length_append, List.foldr_cons, encodeClause_eq,
        List.length_append]
      have h := size_clause_le_body C
      simp only [List.length_cons, List.length_nil]
      omega

/-! ## The instance -/

/-- **`Serialize cnf`** — the canonical CNF layout of the whole development
(`EvalCnfCmd.encodeCnf`: the SAT verifier's own `CNF_STREAM` format), now with a
parser and both size laws. -/
instance instSerializeCnf : Serialize cnf where
  enc := encodeCnf
  dec := decCnf
  dec_enc := decCnf_encodeCnf
  enc_bit := EvalCnfCmd.encodeCnf_bit
  -- the identity form of the no-compression law: `encodeCnf` is long enough
  -- that no polynomial slack is needed (FINDING AT).
  sizeLB := fun n => n
  sizeLB_poly := inOPoly_id
  sizeLB_mono := fun _ _ h => h
  size_le_enc_length := size_le_encodeCnf_length
  encLen := fun n => 5 * n
  encLen_poly := inOPoly_mul (inOPoly_const 5) inOPoly_id
  encLen_mono := fun _ _ h => Nat.mul_le_mul_left 5 h
  enc_length_le := EvalCnfCmd.encodeCnf_length

end CnfSerialize
