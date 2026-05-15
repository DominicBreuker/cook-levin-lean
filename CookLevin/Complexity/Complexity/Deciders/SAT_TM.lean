import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider
import Complexity.Complexity.TMPrimitives
import Complexity.NP.SAT
import Mathlib.Tactic

set_option autoImplicit false

/-! # The SAT decider TM (Step 6 of `PART2.md`)

We build a `FlatTM` that decides `evalCnf a N` on an encoded input
`(N, a) : cnf × assgn`, prove a polynomial time bound, and package
the result as a `DecidesBy` witness suitable for the new
`inTimePolyTM` framework.

This file follows the staged pattern established by
`TMPrimitives.AllFalse`:

1. **Encoding** — concrete `List Nat` layout for `(N, a)` using a
   small fixed alphabet and unary variable indices.
2. **Encoding lemmas** — length bound, accessor lemmas, structural
   identities.
3. **Sub-primitives** — TMs for atomic operations like "scan to the
   next delimiter", "compare two unary words", "advance to next
   clause".
4. **`evalCnfTM`** — the full TM, composed from primitives.
5. **Operational correctness** — `acceptsFlatTM evalCnfTM (encode N a)
   t = true ↔ evalCnf a N = true` for some polynomial time bound `t`.
6. **`DecidesBy` packaging** — wrap into a witness.

This is **incremental work**; this session lands the encoding plus
size-bound lemmas. Later sessions add the TM proper.

### Alphabet

| symbol | meaning                                                 |
|--------|---------------------------------------------------------|
| 0      | end-of-input terminator                                 |
| 1      | unary digit (used in variable indices)                  |
| 2      | positive literal sign                                   |
| 3      | negative literal sign                                   |
| 4      | clause separator inside the CNF                         |
| 5      | "end of CNF / start of assignment" separator            |
| 6      | assignment-element separator                            |

So `sigSAT = 7`.

### Encoding shape

- Literal `(true, v)`  ↦ `2 :: List.replicate v 1`
- Literal `(false, v)` ↦ `3 :: List.replicate v 1`
- Clause `[ℓ₁, …, ℓₖ]`  ↦ enc(ℓ₁) ++ … ++ enc(ℓₖ) ++ [4]
- CNF `[C₁, …, Cₘ]`     ↦ enc(C₁) ++ … ++ enc(Cₘ) ++ [5]
- Assgn `[v₁, …, vₚ]`   ↦ List.replicate v₁ 1 ++ [6] ++ … ++ List.replicate vₚ 1 ++ [6] ++ [0]
- Input `(N, a)`        ↦ enc(N) ++ enc(a)

Note: the CNF terminator `5` doubles as the start-of-assignment
marker, and the input ends in `0` so the head can detect end-of-input.
-/

namespace SAT_TM

/-- Alphabet size. -/
def sigSAT : Nat := 7

/-- Encode a single literal as a sign symbol followed by a unary
representation of its variable index. -/
def encodeLiteral : literal → List Nat
  | (true,  v) => 2 :: List.replicate v 1
  | (false, v) => 3 :: List.replicate v 1

/-- Encode a clause as the concatenation of its literal encodings,
followed by a `4` (clause terminator). -/
def encodeClause (c : clause) : List Nat :=
  (c.map encodeLiteral).flatten ++ [4]

/-- Encode a CNF as the concatenation of its clause encodings, followed
by a `5` (CNF terminator / assignment start). -/
def encodeCnf (N : cnf) : List Nat :=
  (N.map encodeClause).flatten ++ [5]

/-- Encode an assignment as a `6`-separated list of unary variables,
ending with `6` (final element separator) and a `0` (input
terminator). -/
def encodeAssgn : assgn → List Nat
  | [] => [0]
  | v :: vs => List.replicate v 1 ++ 6 :: encodeAssgn vs

/-- Encode an `(N, a)` input pair: CNF followed by assignment. -/
def encodeInput : cnf × assgn → List Nat
  | (N, a) => encodeCnf N ++ encodeAssgn a

/-! ### Length bounds

We need `(encodeInput (N, a)).length ≤ p (encodable.size (N, a))` for
some polynomial `p`. The encoding is linear in the sum of variable
indices plus the structural overhead (delimiters, signs).

For now we bound each component separately. The exact polynomial
appears once we wire the decider into a `DecidesBy` witness. -/

theorem encodeLiteral_length (l : literal) :
    (encodeLiteral l).length = l.2 + 1 := by
  rcases l with ⟨b, v⟩
  cases b
  · show (3 :: List.replicate v 1).length = v + 1
    simp [List.length_replicate]
  · show (2 :: List.replicate v 1).length = v + 1
    simp [List.length_replicate]

theorem encodeClause_length (c : clause) :
    (encodeClause c).length =
      ((c.map encodeLiteral).map List.length).sum + 1 := by
  show ((c.map encodeLiteral).flatten ++ [4]).length = _
  rw [List.length_append, List.length_singleton, List.length_flatten]

theorem encodeCnf_length (N : cnf) :
    (encodeCnf N).length =
      ((N.map encodeClause).map List.length).sum + 1 := by
  show ((N.map encodeClause).flatten ++ [5]).length = _
  rw [List.length_append, List.length_singleton, List.length_flatten]

theorem encodeAssgn_length :
    ∀ (a : assgn),
      (encodeAssgn a).length = a.foldr (fun v acc => v + 1 + acc) 1
  | [] => by
      show ([0] : List Nat).length = 1
      rfl
  | v :: vs => by
      have ih := encodeAssgn_length vs
      show (List.replicate v 1 ++ 6 :: encodeAssgn vs).length =
        (v :: vs).foldr (fun w acc => w + 1 + acc) 1
      rw [List.length_append, List.length_replicate, List.length_cons, ih]
      show v + (vs.foldr (fun w acc => w + 1 + acc) 1 + 1) =
        (v :: vs).foldr (fun w acc => w + 1 + acc) 1
      -- foldr on cons unfolds: (v :: vs).foldr f init = f v (vs.foldr f init)
      show v + (vs.foldr (fun w acc => w + 1 + acc) 1 + 1) =
        v + 1 + vs.foldr (fun w acc => w + 1 + acc) 1
      rw [Nat.add_comm (vs.foldr _ 1) 1, ← Nat.add_assoc]

theorem encodeInput_length (N : cnf) (a : assgn) :
    (encodeInput (N, a)).length = (encodeCnf N).length + (encodeAssgn a).length := by
  show ((encodeCnf N) ++ (encodeAssgn a)).length = _
  rw [List.length_append]

/-! ### Symbol bounds

Every tape symbol the encoding emits is `< sigSAT = 7`. This is what
the SAT TM will rely on when scanning. -/

theorem encodeLiteral_symbols_lt (l : literal) :
    ∀ x ∈ encodeLiteral l, x < sigSAT := by
  rcases l with ⟨b, v⟩
  cases b
  · intro x hx
    show x < 7
    have hx' : x ∈ 3 :: List.replicate v 1 := hx
    rcases List.mem_cons.mp hx' with h | h
    · rw [h]; decide
    · rw [List.mem_replicate.mp h |>.2]; decide
  · intro x hx
    show x < 7
    have hx' : x ∈ 2 :: List.replicate v 1 := hx
    rcases List.mem_cons.mp hx' with h | h
    · rw [h]; decide
    · rw [List.mem_replicate.mp h |>.2]; decide

theorem encodeClause_symbols_lt (c : clause) :
    ∀ x ∈ encodeClause c, x < sigSAT := by
  intro x hx
  show x < 7
  unfold encodeClause at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_flatten.mp h with ⟨L, hL_in, hx_in_L⟩
    rcases List.mem_map.mp hL_in with ⟨l, _, hL_eq⟩
    rw [← hL_eq] at hx_in_L
    exact encodeLiteral_symbols_lt l x hx_in_L
  · rw [List.mem_singleton.mp h]; decide

theorem encodeCnf_symbols_lt (N : cnf) :
    ∀ x ∈ encodeCnf N, x < sigSAT := by
  intro x hx
  show x < 7
  unfold encodeCnf at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_flatten.mp h with ⟨L, hL_in, hx_in_L⟩
    rcases List.mem_map.mp hL_in with ⟨c, _, hL_eq⟩
    rw [← hL_eq] at hx_in_L
    exact encodeClause_symbols_lt c x hx_in_L
  · rw [List.mem_singleton.mp h]; decide

theorem encodeAssgn_symbols_lt :
    ∀ (a : assgn) x, x ∈ encodeAssgn a → x < sigSAT
  | [], x, hx => by
      have : x ∈ ([0] : List Nat) := hx
      rw [List.mem_singleton.mp this]; decide
  | v :: vs, x, hx => by
      have hx' : x ∈ List.replicate v 1 ++ 6 :: encodeAssgn vs := hx
      rcases List.mem_append.mp hx' with h | h
      · rw [List.mem_replicate.mp h |>.2]; decide
      · rcases List.mem_cons.mp h with h6 | hrest
        · rw [h6]; decide
        · exact encodeAssgn_symbols_lt vs x hrest

theorem encodeInput_symbols_lt (N : cnf) (a : assgn) :
    ∀ x ∈ encodeInput (N, a), x < sigSAT := by
  intro x hx
  have hx' : x ∈ encodeCnf N ++ encodeAssgn a := hx
  rcases List.mem_append.mp hx' with h | h
  · exact encodeCnf_symbols_lt N x h
  · exact encodeAssgn_symbols_lt a x h

/-! ### Polynomial size bound

The framework `DecidesBy.encode_size` asks for
`(encode x).length ≤ encodable.size x + 1`. We prove this by walking
the encoding's hierarchy: literal → clause → CNF, and assignment, then
combining via the pair encoding. Each bound is **linear**, not just
polynomial — a pleasant surprise. -/

private theorem literal_size_eq (l : literal) :
    encodable.size l = (if l.1 then 1 else 0) + l.2 + 1 := by
  rcases l with ⟨b, v⟩
  cases b
  · show 0 + v + 1 = (if false then 1 else 0) + v + 1; rfl
  · show 1 + v + 1 = (if true then 1 else 0) + v + 1; rfl

theorem encodeLiteral_length_le (l : literal) :
    (encodeLiteral l).length ≤ encodable.size l := by
  rw [encodeLiteral_length, literal_size_eq]
  -- l.2 + 1 ≤ (if l.1 then 1 else 0) + l.2 + 1
  rcases l with ⟨b, v⟩
  cases b
  · show v + 1 ≤ 0 + v + 1
    rw [Nat.zero_add]
  · show v + 1 ≤ 1 + v + 1
    rw [Nat.add_comm 1 v]
    exact Nat.le_succ _

private theorem List_foldl_acc_le {α : Type _} (w : α → Nat) :
    ∀ (xs : List α) (c d : Nat), c ≤ d →
      xs.foldl (fun acc x => acc + w x + 1) c ≤
        xs.foldl (fun acc x => acc + w x + 1) d
  | [], c, d, h => h
  | x :: xs, c, d, h => by
      show (x :: xs).foldl (fun acc y => acc + w y + 1) c ≤ _
      show xs.foldl (fun acc y => acc + w y + 1) (c + w x + 1) ≤
        xs.foldl (fun acc y => acc + w y + 1) (d + w x + 1)
      exact List_foldl_acc_le w xs _ _ (Nat.add_le_add_right (Nat.add_le_add_right h _) 1)

theorem encodeClause_length_le (c : clause) :
    (encodeClause c).length ≤ encodable.size c + 1 := by
  rw [encodeClause_length]
  -- ((c.map encodeLiteral).map List.length).sum + 1 ≤ encodable.size c + 1
  refine Nat.add_le_add_right ?_ 1
  -- sum of literal-encoding lengths ≤ encodable.size c
  -- encodable.size c = c.foldl (fun acc l => acc + encodable.size l + 1) 0
  -- = sum (encodable.size l + 1) over c, starting at 0
  -- The encoded lengths are bounded by the encodable sizes.
  show ((c.map encodeLiteral).map List.length).sum ≤ encodable.size c
  -- Convert sum of (encodeLiteral _).length to a foldl form.
  induction c with
  | nil => exact Nat.le_refl 0
  | cons l rest ih =>
      have hl := encodeLiteral_length_le l
      show ((encodeLiteral l).length :: ((rest.map encodeLiteral).map List.length)).sum
        ≤ encodable.size (l :: rest)
      rw [List.sum_cons]
      rw [encodable_size_list_cons]
      calc (encodeLiteral l).length + ((rest.map encodeLiteral).map List.length).sum
          ≤ encodable.size l + encodable.size rest := Nat.add_le_add hl ih
        _ ≤ encodable.size l + 1 + encodable.size rest := by
            apply Nat.add_le_add_right
            exact Nat.le_succ _

theorem encodeCnf_length_le (N : cnf) :
    (encodeCnf N).length ≤ encodable.size N + 1 := by
  rw [encodeCnf_length]
  refine Nat.add_le_add_right ?_ 1
  show ((N.map encodeClause).map List.length).sum ≤ encodable.size N
  induction N with
  | nil => exact Nat.le_refl 0
  | cons c rest ih =>
      have hc := encodeClause_length_le c
      show ((encodeClause c).length :: ((rest.map encodeClause).map List.length)).sum
        ≤ encodable.size (c :: rest)
      rw [List.sum_cons, encodable_size_list_cons]
      calc (encodeClause c).length + ((rest.map encodeClause).map List.length).sum
          ≤ (encodable.size c + 1) + encodable.size rest := Nat.add_le_add hc ih

theorem encodeAssgn_length_le :
    ∀ (a : assgn), (encodeAssgn a).length ≤ encodable.size a + 1
  | [] => by
      show ([0] : List Nat).length ≤ 0 + 1
      rfl
  | v :: vs => by
      have ih := encodeAssgn_length_le vs
      show (List.replicate v 1 ++ 6 :: encodeAssgn vs).length ≤
        encodable.size (v :: vs) + 1
      rw [List.length_append, List.length_replicate, List.length_cons,
          encodable_size_list_cons]
      show v + ((encodeAssgn vs).length + 1) ≤ encodable.size v + 1 + encodable.size vs + 1
      have h_size_v : (encodable.size v : Nat) = v := rfl
      rw [h_size_v]
      calc v + ((encodeAssgn vs).length + 1)
          ≤ v + (encodable.size vs + 1 + 1) :=
              Nat.add_le_add_left (Nat.add_le_add_right ih 1) v
        _ = v + 1 + encodable.size vs + 1 := by ring

/-- The headline polynomial size bound for `DecidesBy.encode_size`. -/
theorem encodeInput_length_le (N : cnf) (a : assgn) :
    (encodeInput (N, a)).length ≤ encodable.size (N, a) + 1 := by
  rw [encodeInput_length]
  -- encodable.size (N, a) = encodable.size N + encodable.size a + 1.
  have hpair : encodable.size ((N, a) : cnf × assgn) =
      encodable.size N + encodable.size a + 1 := rfl
  rw [hpair]
  calc (encodeCnf N).length + (encodeAssgn a).length
      ≤ (encodable.size N + 1) + (encodable.size a + 1) :=
          Nat.add_le_add (encodeCnf_length_le N) (encodeAssgn_length_le a)
    _ = encodable.size N + encodable.size a + 1 + 1 := by ring

/-! ## A first SAT-input-based decider: `decideCnfEmpty`

We exercise the new SAT encoding by deciding the simplest non-trivial
predicate on `(cnf × assgn)`: is the CNF empty? In our encoding,
`encodeInput ([], a) = [5] ++ encodeAssgn a`, so the question
reduces to "does the input tape start with symbol `5`?".

This is structurally the simplest possible single-tape decider — read
position 0, branch on the symbol. It exercises:

- the `SAT_TM` alphabet conventions and encoding,
- the `DecidesBy` multi-tape API (with `M.tapes = 1`),
- the operational-correctness style established by `verdictTM`.
-/

namespace CnfEmpty

/-- The 3-state TM. State 0 reads position 0; state 1 is accept-halt;
state 2 is reject-halt. -/
def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 3
  trans :=
    let mkAccept : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some 5]
        dst_state := 1
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let mkRejectSymbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some v]
        dst_state := 2
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let mkRejectNone : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [none]
        dst_state := 2
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    mkAccept :: mkRejectNone ::
      ((List.range sigSAT).filter (fun v => decide (v ≠ 5))).map mkRejectSymbol
  start := 0
  halt := [false, true, true]

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 3; decide
  · show [false, true, true].length = 3; rfl
  · intro entry hentry
    have hentry' : entry ∈ TM.trans := hentry
    show flatTMTransEntryValid TM entry
    -- Three sub-cases: accept entry, none-entry, reject-symbol entry.
    unfold TM at hentry'
    rcases List.mem_cons.mp hentry' with hAccept | hRest
    · -- accept entry
      subst hAccept
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 3; decide
      · show 1 < 3; decide
      · intro x hx
        simp at hx
        subst hx
        show 5 < sigSAT; decide
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_cons.mp hRest with hNone | hRej
      · -- none-reject entry
        subst hNone
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp at hx; subst hx; trivial
        · intro x hx; simp at hx; subst hx; trivial
      · -- reject-symbol entry for some v ∈ filtered range
        rcases List.mem_map.mp hRej with ⟨v, hv, hmk⟩
        subst hmk
        have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp at hx; subst hx; exact hvlt
        · intro x hx; simp at hx; subst hx; trivial

/-- The encoded input for `(N, a) = ([], a)` starts with symbol `5`. -/
theorem encodeInput_empty_cnf_head (a : assgn) :
    (encodeInput ([], a)).head? = some 5 := by
  show (encodeCnf [] ++ encodeAssgn a).head? = some 5
  -- encodeCnf [] = [5] (by the case [] => [5] terminator)
  show ((([] : cnf).map encodeClause).flatten ++ [5] ++ encodeAssgn a).head? = some 5
  rw [List.map_nil, List.flatten_nil, List.nil_append]
  -- ([5] ++ encodeAssgn a).head? = some 5
  cases a
  · rfl
  · rfl

/-- For `N = C :: rest`, the encoded input's first symbol is the first
symbol of `encodeClause C`, which is `4` (if `C = []`) or a sign byte
`2`/`3` (otherwise). In every case it is `≠ 5`. -/
theorem encodeInput_nonempty_cnf_head (C : clause) (rest : cnf) (a : assgn) :
    (encodeInput (C :: rest, a)).head? ≠ some 5 := by
  cases C with
  | nil =>
      have h_head : (encodeInput ([] :: rest, a)).head? = some 4 := rfl
      rw [h_head]
      intro h
      injection h with h1
      exact absurd h1 (by decide)
  | cons l ls =>
      rcases l with ⟨b, v⟩
      cases b
      · have h_head : (encodeInput (((false, v) :: ls) :: rest, a)).head? = some 3 := rfl
        rw [h_head]
        intro h
        injection h with h1
        exact absurd h1 (by decide)
      · have h_head : (encodeInput (((true, v) :: ls) :: rest, a)).head? = some 2 := rfl
        rw [h_head]
        intro h
        injection h with h1
        exact absurd h1 (by decide)

/-! ### Operational correctness for `CnfEmpty.TM`

We need two step lemmas:

- if the tape's first symbol is `some 5`, one step lands in state 1
  (accept);
- if the tape's first symbol is `some v` with `v ≠ 5, v < sigSAT`,
  one step lands in state 2 (reject);
- if the tape is empty (head returns `none`), one step lands in state
  2 (reject).
-/

private def acceptEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 5]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def rejectNoneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def rejectSymbolEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans = acceptEntry :: rejectNoneEntry ::
      ((List.range sigSAT).filter (fun v => decide (v ≠ 5))).map rejectSymbolEntry := rfl

/-- Single-tape `applyTransitionEntry` for our shape (write `[none]`,
move `Nmove`). The new config keeps the tape unchanged. -/
private theorem applyEntry_singleTape
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

theorem TM_step_match
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ acceptEntry = _
  exact applyEntry_singleTape 0 1 left right head (some 5)

theorem TM_step_reject_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNotMatchAcc : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatchNone : entryMatchesConfig rejectNoneEntry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNotMatchAcc, List.find?_cons, hMatchNone]
  show applyTransitionEntry _ rejectNoneEntry = _
  exact applyEntry_singleTape 0 2 left right head none

private theorem find_rejectSymbolEntry_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_ne : v ≠ 5)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter (fun w => decide (w ≠ 5))).map rejectSymbolEntry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }) =
      some (rejectSymbolEntry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 5)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_ne
  -- Induct on the filtered list, similar to `find_continueEntry_match` in TMPrimitives.
  generalize hList : (List.range sigSAT).filter (fun w => decide (w ≠ 5)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (rejectSymbolEntry w :: ws.map rejectSymbolEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (rejectSymbolEntry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · -- w ≠ v: this entry doesn't match.
        have hNotMatch : entryMatchesConfig (rejectSymbolEntry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h
            injection h with h1
            injection h1 with h2
            exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

theorem TM_step_reject_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_ne : v ≠ 5)
    (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  -- acceptEntry doesn't match (target 5 ≠ v)
  have hNotMatchAcc : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1
      injection h1 with h2
      exact h_ne h2.symm
    simp [h_ne_some]
  -- rejectNoneEntry doesn't match (none vs some v)
  have hNotMatchNone : entryMatchesConfig rejectNoneEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hFind := find_rejectSymbolEntry_match left right head v h_head_lt h_get h_ne h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNotMatchAcc, List.find?_cons, hNotMatchNone, hFind]
  show applyTransitionEntry _ (rejectSymbolEntry v) = _
  exact applyEntry_singleTape 0 2 left right head (some v)

/-- One-step run from state 0 with a non-halting start: just steps. -/
private theorem run_one (left right : List Nat) (head : Nat) (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM 1 TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg' := by
  show (if haltingStateReached TM
            { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM 0 TM cfg'') = some cfg'
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

/-- The TM-backed decider for "the CNF in the encoded input is empty". -/
def decider : DecidesBy
    (fun Na : cnf × assgn => Na.1 = [])
    (fun _ => 1) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 1
  rejectState := 2
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ hN_empty
    subst hN_empty
    -- encodeInput ([], a) = 5 :: encodeAssgn a definitionally.
    -- So position 0 is `5`, the TM reads it, and the run lands in state 1.
    have h_head_lt : (0 : Nat) < (encodeInput ([], a)).length := by
      show 0 < (5 :: encodeAssgn a).length
      exact Nat.zero_lt_succ _
    have h_get : (encodeInput ([], a)).get ⟨0, h_head_lt⟩ = 5 := rfl
    have h_step :=
      TM_step_match [] (encodeInput ([], a)) 0 h_head_lt h_get
    have h_run := run_one [] (encodeInput ([], a)) 0
      { state_idx := 1, tapes := [([], 0, encodeInput ([], a))] } h_step
    exact ⟨_, h_run, rfl, rfl⟩
  decides_neg := by
    rintro ⟨N, a⟩ hN_nonempty
    cases N with
    | nil => exact absurd rfl hN_nonempty
    | cons C rest =>
        -- We case on the shape of `C` and the first literal sign to extract
        -- the first symbol value `v ∈ {2, 3, 4}` (each `< sigSAT`, each `≠ 5`).
        cases C with
        | nil =>
            -- encodeInput (([] : clause) :: rest, a) = 4 :: ... definitionally.
            have h_head_lt : (0 : Nat) < (encodeInput (([] : clause) :: rest, a)).length := by
              show 0 < (4 :: ((rest.map encodeClause).flatten ++ [5] ++ encodeAssgn a)).length
              exact Nat.zero_lt_succ _
            have h_get : (encodeInput (([] : clause) :: rest, a)).get ⟨0, h_head_lt⟩ = 4 := rfl
            have h_step := TM_step_reject_symbol []
              (encodeInput (([] : clause) :: rest, a)) 0 4 h_head_lt h_get
              (by decide) (by decide)
            have h_run := run_one [] (encodeInput (([] : clause) :: rest, a)) 0 _ h_step
            exact ⟨_, h_run, rfl, rfl⟩
        | cons l ls =>
            rcases l with ⟨b, v⟩
            cases b
            · -- (false, v) → first symbol is 3.
              have h_head_lt :
                  (0 : Nat) < (encodeInput (((false, v) :: ls) :: rest, a)).length := by
                show 0 < (3 :: _).length
                exact Nat.zero_lt_succ _
              have h_get :
                  (encodeInput (((false, v) :: ls) :: rest, a)).get ⟨0, h_head_lt⟩ = 3 := rfl
              have h_step := TM_step_reject_symbol []
                (encodeInput (((false, v) :: ls) :: rest, a)) 0 3 h_head_lt h_get
                (by decide) (by decide)
              have h_run :=
                run_one [] (encodeInput (((false, v) :: ls) :: rest, a)) 0 _ h_step
              exact ⟨_, h_run, rfl, rfl⟩
            · -- (true, v) → first symbol is 2.
              have h_head_lt :
                  (0 : Nat) < (encodeInput (((true, v) :: ls) :: rest, a)).length := by
                show 0 < (2 :: _).length
                exact Nat.zero_lt_succ _
              have h_get :
                  (encodeInput (((true, v) :: ls) :: rest, a)).get ⟨0, h_head_lt⟩ = 2 := rfl
              have h_step := TM_step_reject_symbol []
                (encodeInput (((true, v) :: ls) :: rest, a)) 0 2 h_head_lt h_get
                (by decide) (by decide)
              have h_run :=
                run_one [] (encodeInput (((true, v) :: ls) :: rest, a)) 0 _ h_step
              exact ⟨_, h_run, rfl, rfl⟩

/-- The constant time bound `n ↦ 1` is monotonic and polynomial. -/
theorem timeBound_inOPoly : inOPoly (fun _ : Nat => 1) :=
  inOPoly_const 1

theorem timeBound_monotonic : monotonic (fun _ : Nat => 1) := fun _ _ _ => Nat.le_refl 1

/-- "The CNF is empty" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfEmpty :
    inTimePolyTM (fun Na : cnf × assgn => Na.1 = []) :=
  ⟨fun _ => 1, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end CnfEmpty

/-! ## `CnfEmptyAssgnEmpty`: a 2-step decider for `N = [] ∧ a = []`

A natural next stepping stone after `CnfEmpty`. This decider exercises:
- a **multi-step** run (2 reads, not 1);
- **head advancement** between steps (`Rmove` moves head from 0 to 1);
- a **sequential state transition** (state 0 → state 1 → final state).

The predicate `Na.1 = [] ∧ Na.2 = []` is equivalent to the first two
encoded symbols being exactly `[5, 0]`:
- `5` (CNF terminator) at position 0 iff `N = []`.
- `0` (input terminator) at position 1 iff additionally `a = []`.

These two symbols are sufficient because for `N = [] ∧ a ≠ []`, the
symbol after the `5` is either `1` (first unary digit, when `v_1 ≥ 1`)
or `6` (separator, when `v_1 = 0`), never `0`. -/

namespace CnfEmptyAssgnEmpty

/-- The 4-state TM. State 0 = read pos 0; state 1 = read pos 1
(after one `Rmove`); state 2 = accept halt; state 3 = reject halt. -/
def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 4
  trans :=
    let s0_advance : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some 5]
        dst_state := 1
        dst_write_vals := [none]
        move_dirs := [TMMove.Rmove] }
    let s0_reject_none : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [none]
        dst_state := 3
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let s0_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some v]
        dst_state := 3
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let s1_accept : FlatTMTransEntry :=
      { src_state := 1
        src_tape_vals := [some 0]
        dst_state := 2
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let s1_reject_none : FlatTMTransEntry :=
      { src_state := 1
        src_tape_vals := [none]
        dst_state := 3
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let s1_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 1
        src_tape_vals := [some v]
        dst_state := 3
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    s0_advance :: s0_reject_none :: s1_accept :: s1_reject_none ::
      (((List.range sigSAT).filter (fun v => decide (v ≠ 5))).map s0_reject_symbol ++
        ((List.range sigSAT).filter (fun v => decide (v ≠ 0))).map s1_reject_symbol)
  start := 0
  halt := [false, false, true, true]

private def s0_advance_entry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 5]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def s0_reject_none_entry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def s0_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def s1_accept_entry : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some 0]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def s1_reject_none_entry : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [none]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def s1_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some v]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans =
      s0_advance_entry :: s0_reject_none_entry ::
      s1_accept_entry :: s1_reject_none_entry ::
      (((List.range sigSAT).filter (fun v => decide (v ≠ 5))).map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter (fun v => decide (v ≠ 0))).map s1_reject_symbol_entry) := rfl

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 4; decide
  · show [false, false, true, true].length = 4; rfl
  · intro entry hentry
    show flatTMTransEntryValid TM entry
    rw [TM_trans_eq] at hentry
    -- Top four: s0_advance, s0_reject_none, s1_accept, s1_reject_none.
    rcases List.mem_cons.mp hentry with h | hRest1
    · -- s0_advance
      subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 4; decide
      · show 1 < 4; decide
      · intro x hx
        have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'
        subst hx'
        show 5 < sigSAT; decide
      · intro x hx
        have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'
        subst hx'
        trivial
    · rcases List.mem_cons.mp hRest1 with h | hRest2
      · -- s0_reject_none
        subst h
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 4; decide
        · show 3 < 4; decide
        · intro x hx
          have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'
          subst hx'
          trivial
        · intro x hx
          have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'
          subst hx'
          trivial
      · rcases List.mem_cons.mp hRest2 with h | hRest3
        · -- s1_accept
          subst h
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 4; decide
          · show 2 < 4; decide
          · intro x hx
            have hx' : x ∈ ([some 0] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'
            subst hx'
            show 0 < sigSAT; decide
          · intro x hx
            have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'
            subst hx'
            trivial
        · rcases List.mem_cons.mp hRest3 with h | hAppend
          · -- s1_reject_none
            subst h
            refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
            · show 1 < 4; decide
            · show 3 < 4; decide
            · intro x hx
              have hx' : x ∈ ([none] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'
              subst hx'
              trivial
            · intro x hx
              have hx' : x ∈ ([none] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'
              subst hx'
              trivial
          · rcases List.mem_append.mp hAppend with hS0Rej | hS1Rej
            · -- s0_reject_symbol from filtered range
              rcases List.mem_map.mp hS0Rej with ⟨v, hv, hmk⟩
              subst hmk
              have hvlt : v < sigSAT :=
                List.mem_range.mp (List.mem_filter.mp hv).1
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 0 < 4; decide
              · show 3 < 4; decide
              · intro x hx
                have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'
                subst hx'
                exact hvlt
              · intro x hx
                have hx' : x ∈ ([none] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'
                subst hx'
                trivial
            · -- s1_reject_symbol from filtered range
              rcases List.mem_map.mp hS1Rej with ⟨v, hv, hmk⟩
              subst hmk
              have hvlt : v < sigSAT :=
                List.mem_range.mp (List.mem_filter.mp hv).1
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 1 < 4; decide
              · show 3 < 4; decide
              · intro x hx
                have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'
                subst hx'
                exact hvlt
              · intro x hx
                have hx' : x ∈ ([none] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'
                subst hx'
                trivial

/-! ### Operational correctness for `CnfEmptyAssgnEmpty.TM`

Six step lemmas, two per state, covering the cases (sym = matching
symbol, sym = some v non-matching, sym = none). We use the `Rmove`
variant only for the state-0 → state-1 advance step. -/

/-- Single-tape `applyTransitionEntry` for the `Nmove` (no-move) case. -/
private theorem applyEntry_Nmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

/-- Single-tape `applyTransitionEntry` for the `Rmove` (move-right) case.
The head advances by 1; the underlying `right` list is unchanged. -/
private theorem applyEntry_Rmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Rmove] } =
      some { state_idx := new_state, tapes := [(left, head + 1, right)] } := rfl

/-- State 0, current symbol `5`: advance right, go to state 1. -/
theorem TM_step_advance_5
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s0_advance_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_advance_entry = _
  exact applyEntry_Rmove 0 1 left right head (some 5)

/-- State 0, head off the right end (no current symbol): reject. -/
theorem TM_step_reject_state_0_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNotMatch_advance : entryMatchesConfig s0_advance_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatch_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNotMatch_advance,
      List.find?_cons, hMatch_none]
  show applyTransitionEntry _ s0_reject_none_entry = _
  exact applyEntry_Nmove 0 3 left right head none

/-- Helper: in the appended `(s0_reject_symbol :: s1_reject_symbol)` lists,
the first match for `(state=0, sym=some v)` with `v ≠ 5, v < sigSAT` is
`s0_reject_symbol_entry v`. -/
private theorem find_s0_reject_symbol_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 5) (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter (fun w => decide (w ≠ 5))).map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter (fun w => decide (w ≠ 0))).map s1_reject_symbol_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_reject_symbol_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 5)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_ne
  -- Walk through the first appended list inductively.
  generalize hList : (List.range sigSAT).filter (fun w => decide (w ≠ 5)) = L0
  rw [hList] at hvInFilter
  clear hList
  induction L0 with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_reject_symbol_entry w :: (ws.map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter (fun w => decide (w ≠ 0))).map s1_reject_symbol_entry)) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_reject_symbol_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_reject_symbol_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h
            injection h with h1
            injection h1 with h2
            exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 0, current symbol `some v` with `v ≠ 5`: reject. -/
theorem TM_step_reject_state_0_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 5) (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNot_advance : entryMatchesConfig s0_advance_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne_some]
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  -- s1_accept has src_state = 1, not 0 — doesn't match.
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hFind := find_s0_reject_symbol_match left right head v h_head_lt h_get h_ne h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hNot_s1_none, hFind]
  show applyTransitionEntry _ (s0_reject_symbol_entry v) = _
  exact applyEntry_Nmove 0 3 left right head (some v)

/-- State 1, current symbol `0`: accept. -/
theorem TM_step_accept_0
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 0
    rw [dif_pos h_head_lt, h_get]
  -- s0_advance (state 0): doesn't match state 1.
  have hNot_advance : entryMatchesConfig s0_advance_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hMatch : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_accept_entry = _
  exact applyEntry_Nmove 1 2 left right head (some 0)

/-- State 1, head off the right end (no current symbol): reject. -/
theorem TM_step_reject_state_1_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNot_advance : entryMatchesConfig s0_advance_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 0] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatch : entryMatchesConfig s1_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_reject_none_entry = _
  exact applyEntry_Nmove 1 3 left right head none

/-- Helper for state 1: filter past the entire `s0_reject_symbol` block
(every entry has `src_state = 0 ≠ 1`), then find the first
`s1_reject_symbol_entry v`. -/
private theorem find_s1_reject_symbol_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 0) (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter (fun w => decide (w ≠ 5))).map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter (fun w => decide (w ≠ 0))).map s1_reject_symbol_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 1, tapes := [(left, head, right)] }) =
      some (s1_reject_symbol_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 0)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_ne
  -- Step 1: walk through the s0_reject_symbol block. None match (state mismatch).
  rw [List.find?_append]
  have hFirstNone :
      (((List.range sigSAT).filter (fun w => decide (w ≠ 5))).map
          s0_reject_symbol_entry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }) = none := by
    -- Every entry in this list has src_state = 0, can't match state 1.
    generalize hL0 : (List.range sigSAT).filter (fun w => decide (w ≠ 5)) = L0
    clear hL0
    induction L0 with
    | nil => rfl
    | cons w ws ih =>
        show List.find? _ (s0_reject_symbol_entry w :: ws.map s0_reject_symbol_entry) = _
        rw [List.find?_cons]
        have hNotMatch : entryMatchesConfig (s0_reject_symbol_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rfl
        rw [hNotMatch]
        exact ih
  rw [hFirstNone, Option.none_or]
  -- Step 2: induction within the s1_reject_symbol block.
  generalize hList : (List.range sigSAT).filter (fun w => decide (w ≠ 0)) = L1
  rw [hList] at hvInFilter
  clear hList
  induction L1 with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s1_reject_symbol_entry w :: ws.map s1_reject_symbol_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s1_reject_symbol_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = true := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((1 : Nat) == 1) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s1_reject_symbol_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = false := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h
            injection h with h1
            injection h1 with h2
            exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 1, current symbol `some v` with `v ≠ 0`: reject. -/
theorem TM_step_reject_state_1_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 0) (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNot_advance : entryMatchesConfig s0_advance_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 0] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne_some]
  have hNot_s1_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hFind := find_s1_reject_symbol_match left right head v h_head_lt h_get h_ne h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hNot_s1_none, hFind]
  show applyTransitionEntry _ (s1_reject_symbol_entry v) = _
  exact applyEntry_Nmove 1 3 left right head (some v)

/-! ### Run helpers and the decider -/

/-- Two consecutive non-halting steps (state 0 → state 1 → final). -/
private theorem run_two_steps
    (start_left start_right : List Nat) (start_head : Nat)
    (mid_left mid_right : List Nat) (mid_head : Nat)
    (final_state : Nat) (final_left final_right : List Nat) (final_head : Nat)
    (h_step1 : stepFlatTM TM
        { state_idx := 0, tapes := [(start_left, start_head, start_right)] } =
      some { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] })
    (h_step2 : stepFlatTM TM
        { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] } =
      some { state_idx := final_state,
             tapes := [(final_left, final_head, final_right)] }) :
    runFlatTM 2 TM
        { state_idx := 0, tapes := [(start_left, start_head, start_right)] } =
      some { state_idx := final_state,
             tapes := [(final_left, final_head, final_right)] } := by
  show (if haltingStateReached TM
            { state_idx := 0, tapes := [(start_left, start_head, start_right)] } = true then
          some { state_idx := 0, tapes := [(start_left, start_head, start_right)] }
        else
          match stepFlatTM TM
              { state_idx := 0, tapes := [(start_left, start_head, start_right)] } with
          | none => some { state_idx := 0, tapes := [(start_left, start_head, start_right)] }
          | some cfg' => runFlatTM 1 TM cfg') = _
  have h_not_halt_0 : haltingStateReached TM
      { state_idx := 0, tapes := [(start_left, start_head, start_right)] } = false := rfl
  rw [h_not_halt_0, h_step1]
  show (if haltingStateReached TM
            { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] } = true then
          some { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] }
        else
          match stepFlatTM TM
              { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] } with
          | none => some { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] }
          | some cfg' => runFlatTM 0 TM cfg') = _
  have h_not_halt_1 : haltingStateReached TM
      { state_idx := 1, tapes := [(mid_left, mid_head, mid_right)] } = false := rfl
  rw [h_not_halt_1, h_step2]
  rfl

/-- One non-halting step followed by a halt at state 3 (early-reject). -/
private theorem run_two_steps_halt_early
    (start_left start_right : List Nat) (start_head : Nat)
    (final_left final_right : List Nat) (final_head : Nat)
    (h_step : stepFlatTM TM
        { state_idx := 0, tapes := [(start_left, start_head, start_right)] } =
      some { state_idx := 3,
             tapes := [(final_left, final_head, final_right)] }) :
    runFlatTM 2 TM
        { state_idx := 0, tapes := [(start_left, start_head, start_right)] } =
      some { state_idx := 3,
             tapes := [(final_left, final_head, final_right)] } := by
  show (if haltingStateReached TM
            { state_idx := 0, tapes := [(start_left, start_head, start_right)] } = true then
          some { state_idx := 0, tapes := [(start_left, start_head, start_right)] }
        else
          match stepFlatTM TM
              { state_idx := 0, tapes := [(start_left, start_head, start_right)] } with
          | none => some { state_idx := 0, tapes := [(start_left, start_head, start_right)] }
          | some cfg' => runFlatTM 1 TM cfg') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(start_left, start_head, start_right)] } = false := rfl
  rw [h_not_halt, h_step]
  exact runFlatTM_of_halting TM
    { state_idx := 3, tapes := [(final_left, final_head, final_right)] } 1 rfl

/-- The TM-backed decider for "the CNF AND the assignment are both empty". -/
def decider : DecidesBy
    (fun Na : cnf × assgn => Na.1 = [] ∧ Na.2 = [])
    (fun _ => 2) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 2
  rejectState := 3
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ ⟨hN, ha⟩
    subst hN
    subst ha
    have h_head_lt_0 : (0 : Nat) < (encodeInput ([], [])).length := by
      show 0 < (5 :: ([0] : List Nat)).length
      exact Nat.zero_lt_succ _
    have h_get_0 : (encodeInput ([], [])).get ⟨0, h_head_lt_0⟩ = 5 := rfl
    have h_step1 :=
      TM_step_advance_5 [] (encodeInput ([], [])) 0 h_head_lt_0 h_get_0
    have h_head_lt_1 : (1 : Nat) < (encodeInput ([], [])).length := by
      show 1 < (5 :: ([0] : List Nat)).length
      exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
    have h_get_1 : (encodeInput ([], [])).get ⟨1, h_head_lt_1⟩ = 0 := rfl
    have h_step2 :=
      TM_step_accept_0 [] (encodeInput ([], [])) 1 h_head_lt_1 h_get_1
    have h_run := run_two_steps
      [] (encodeInput ([], [])) 0
      [] (encodeInput ([], [])) 1
      2 [] (encodeInput ([], [])) 1
      h_step1 h_step2
    exact ⟨_, h_run, rfl, rfl⟩
  decides_neg := by
    rintro ⟨N, a⟩ hNot_both_empty
    cases N with
    | nil =>
        cases a with
        | nil => exact absurd ⟨rfl, rfl⟩ hNot_both_empty
        | cons v vs =>
            -- N = [] ∧ a = v :: vs. Position 0 = 5, position 1 ∈ {1, 6}.
            have h_head_lt_0 : (0 : Nat) < (encodeInput ([], v :: vs)).length := by
              show 0 < (5 :: _).length
              exact Nat.zero_lt_succ _
            have h_get_0 :
                (encodeInput ([], v :: vs)).get ⟨0, h_head_lt_0⟩ = 5 := rfl
            have h_step1 :=
              TM_step_advance_5 [] (encodeInput ([], v :: vs)) 0 h_head_lt_0 h_get_0
            cases v with
            | zero =>
                have h_head_lt_1 : (1 : Nat) < (encodeInput ([], 0 :: vs)).length := by
                  show 1 < (5 :: 6 :: encodeAssgn vs).length
                  exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
                have h_get_1 :
                    (encodeInput ([], 0 :: vs)).get ⟨1, h_head_lt_1⟩ = 6 := rfl
                have h_step2 := TM_step_reject_state_1_symbol []
                  (encodeInput ([], 0 :: vs)) 1 6 h_head_lt_1 h_get_1
                  (by decide) (by decide)
                have h_run := run_two_steps
                  [] (encodeInput ([], 0 :: vs)) 0
                  [] (encodeInput ([], 0 :: vs)) 1
                  3 [] (encodeInput ([], 0 :: vs)) 1
                  h_step1 h_step2
                exact ⟨_, h_run, rfl, rfl⟩
            | succ w =>
                have h_head_lt_1 :
                    (1 : Nat) < (encodeInput ([], (w + 1) :: vs)).length := by
                  show 1 < (5 :: 1 :: (List.replicate w 1 ++ 6 :: encodeAssgn vs)).length
                  exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
                have h_get_1 :
                    (encodeInput ([], (w + 1) :: vs)).get ⟨1, h_head_lt_1⟩ = 1 := rfl
                have h_step2 := TM_step_reject_state_1_symbol []
                  (encodeInput ([], (w + 1) :: vs)) 1 1 h_head_lt_1 h_get_1
                  (by decide) (by decide)
                have h_run := run_two_steps
                  [] (encodeInput ([], (w + 1) :: vs)) 0
                  [] (encodeInput ([], (w + 1) :: vs)) 1
                  3 [] (encodeInput ([], (w + 1) :: vs)) 1
                  h_step1 h_step2
                exact ⟨_, h_run, rfl, rfl⟩
    | cons C rest =>
        cases C with
        | nil =>
            -- Position 0 = 4.
            have h_head_lt_0 :
                (0 : Nat) < (encodeInput (([] : clause) :: rest, a)).length := by
              show 0 < (4 :: _).length
              exact Nat.zero_lt_succ _
            have h_get_0 :
                (encodeInput (([] : clause) :: rest, a)).get ⟨0, h_head_lt_0⟩ = 4 := rfl
            have h_step := TM_step_reject_state_0_symbol []
              (encodeInput (([] : clause) :: rest, a)) 0 4 h_head_lt_0 h_get_0
              (by decide) (by decide)
            have h_run := run_two_steps_halt_early
              [] (encodeInput (([] : clause) :: rest, a)) 0
              [] (encodeInput (([] : clause) :: rest, a)) 0
              h_step
            exact ⟨_, h_run, rfl, rfl⟩
        | cons l ls =>
            rcases l with ⟨b, v⟩
            cases b
            · have h_head_lt_0 :
                  (0 : Nat) < (encodeInput (((false, v) :: ls) :: rest, a)).length := by
                show 0 < (3 :: _).length
                exact Nat.zero_lt_succ _
              have h_get_0 :
                  (encodeInput (((false, v) :: ls) :: rest, a)).get ⟨0, h_head_lt_0⟩ = 3 := rfl
              have h_step := TM_step_reject_state_0_symbol []
                (encodeInput (((false, v) :: ls) :: rest, a)) 0 3 h_head_lt_0 h_get_0
                (by decide) (by decide)
              have h_run := run_two_steps_halt_early
                [] (encodeInput (((false, v) :: ls) :: rest, a)) 0
                [] (encodeInput (((false, v) :: ls) :: rest, a)) 0
                h_step
              exact ⟨_, h_run, rfl, rfl⟩
            · have h_head_lt_0 :
                  (0 : Nat) < (encodeInput (((true, v) :: ls) :: rest, a)).length := by
                show 0 < (2 :: _).length
                exact Nat.zero_lt_succ _
              have h_get_0 :
                  (encodeInput (((true, v) :: ls) :: rest, a)).get ⟨0, h_head_lt_0⟩ = 2 := rfl
              have h_step := TM_step_reject_state_0_symbol []
                (encodeInput (((true, v) :: ls) :: rest, a)) 0 2 h_head_lt_0 h_get_0
                (by decide) (by decide)
              have h_run := run_two_steps_halt_early
                [] (encodeInput (((true, v) :: ls) :: rest, a)) 0
                [] (encodeInput (((true, v) :: ls) :: rest, a)) 0
                h_step
              exact ⟨_, h_run, rfl, rfl⟩

theorem timeBound_inOPoly : inOPoly (fun _ : Nat => 2) :=
  inOPoly_const 2

theorem timeBound_monotonic : monotonic (fun _ : Nat => 2) :=
  fun _ _ _ => Nat.le_refl 2

/-- "The CNF and the assignment are both empty" is in TM-backed
polynomial time. -/
theorem inTimePolyTM_cnfEmptyAssgnEmpty :
    inTimePolyTM (fun Na : cnf × assgn => Na.1 = [] ∧ Na.2 = []) :=
  ⟨fun _ => 2, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end CnfEmptyAssgnEmpty

/-! ## `AssgnEmpty`: a scan-loop decider for `a = []`

This is the first decider that uses an **inductive scan-loop**. The
TM walks past the entire CNF encoding (whose interior symbols are
all in `{1, 2, 3, 4}`), advances past the `5` terminator, then
checks the next symbol — which is `0` iff the assignment is empty.

State diagram:
- State 0 = scan. On `{1,2,3,4}` advance right, stay in state 0.
  On `5` advance right, go to state 1. On `{0, 6}` or `none`, go
  to state 3 (reject — shouldn't happen for valid encodings).
- State 1 = check. On `0` go to state 2 (accept). On any other
  symbol or `none`, go to state 3 (reject).
- State 2 = accept halt.
- State 3 = reject halt.

The scan-loop bound: `(encodeCnf N).length` steps walk through the
CNF, one more step does the final check. So time bound is
`encodable.size (N, a) + 2`, polynomial in input size. -/

namespace AssgnEmpty

def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 4
  trans :=
    let s0_advance_5 : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_none : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [none], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_accept : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 0], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_reject_none : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [none], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_continue (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 0,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some v], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    s0_advance_5 :: s0_reject_none :: s1_accept :: s1_reject_none ::
      (((List.range sigSAT).filter
            (fun v => decide (v ≠ 0 ∧ v ≠ 5 ∧ v ≠ 6))).map s0_continue ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 6))).map s0_reject_symbol ++
        ((List.range sigSAT).filter
            (fun v => decide (v ≠ 0))).map s1_reject_symbol)
  start := 0
  halt := [false, false, true, true]

private def s0_advance_5_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_none_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [none], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_accept_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 0], dst_state := 2,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_reject_none_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [none], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_continue_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 0,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some v], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans =
      s0_advance_5_entry :: s0_reject_none_entry ::
      s1_accept_entry :: s1_reject_none_entry ::
      (((List.range sigSAT).filter
            (fun v => decide (v ≠ 0 ∧ v ≠ 5 ∧ v ≠ 6))).map s0_continue_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 6))).map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v ≠ 0))).map s1_reject_symbol_entry) := rfl

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 4; decide
  · show [false, false, true, true].length = 4; rfl
  · intro entry hentry
    show flatTMTransEntryValid TM entry
    rw [TM_trans_eq] at hentry
    rcases List.mem_cons.mp hentry with h | hRest1
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 4; decide
      · show 1 < 4; decide
      · intro x hx
        have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 5 < sigSAT; decide
      · intro x hx
        have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    · rcases List.mem_cons.mp hRest1 with h | hRest2
      · subst h
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 4; decide
        · show 3 < 4; decide
        · intro x hx
          have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; trivial
        · intro x hx
          have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; trivial
      · rcases List.mem_cons.mp hRest2 with h | hRest3
        · subst h
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 4; decide
          · show 2 < 4; decide
          · intro x hx
            have hx' : x ∈ ([some 0] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; show 0 < sigSAT; decide
          · intro x hx
            have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; trivial
        · rcases List.mem_cons.mp hRest3 with h | hAppend
          · subst h
            refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
            · show 1 < 4; decide
            · show 3 < 4; decide
            · intro x hx
              have hx' : x ∈ ([none] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'; subst hx'; trivial
            · intro x hx
              have hx' : x ∈ ([none] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'; subst hx'; trivial
          · -- (S0c_block ++ S0r_block) ++ S1r_block; left-associative.
            rcases List.mem_append.mp hAppend with hLeft | hS1Rej
            · rcases List.mem_append.mp hLeft with hCont | hS0Rej
              · -- s0_continue from filter (v ∈ {1,2,3,4})
                rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
                subst hmk
                have hvlt : v < sigSAT :=
                  List.mem_range.mp (List.mem_filter.mp hv).1
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 0 < 4; decide
                · show 0 < 4; decide
                · intro x hx
                  have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                · intro x hx
                  have hx' : x ∈ ([none] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; trivial
              · -- s0_reject_symbol from filter (v ∈ {0, 6})
                rcases List.mem_map.mp hS0Rej with ⟨v, hv, hmk⟩
                subst hmk
                have hvlt : v < sigSAT :=
                  List.mem_range.mp (List.mem_filter.mp hv).1
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 0 < 4; decide
                · show 3 < 4; decide
                · intro x hx
                  have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                · intro x hx
                  have hx' : x ∈ ([none] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; trivial
            · -- s1_reject_symbol from filter (v ≠ 0)
              rcases List.mem_map.mp hS1Rej with ⟨v, hv, hmk⟩
              subst hmk
              have hvlt : v < sigSAT :=
                List.mem_range.mp (List.mem_filter.mp hv).1
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 1 < 4; decide
              · show 3 < 4; decide
              · intro x hx
                have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
              · intro x hx
                have hx' : x ∈ ([none] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'; subst hx'; trivial

/-! ### Step lemmas for `AssgnEmpty.TM` -/

/-- Single-tape `applyTransitionEntry` for the `Nmove` (no-move) case. -/
private theorem applyEntry_Nmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

/-- Single-tape `applyTransitionEntry` for the `Rmove` (move-right) case. -/
private theorem applyEntry_Rmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Rmove] } =
      some { state_idx := new_state, tapes := [(left, head + 1, right)] } := rfl

/-- State 0, sym = `some 5`: advance right, go to state 1. -/
theorem TM_step_advance_5
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_advance_5_entry = _
  exact applyEntry_Rmove 0 1 left right head (some 5)

/-- State 0, sym = `none` (off the right end): reject. -/
theorem TM_step_reject_s0_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatch : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_reject_none_entry = _
  exact applyEntry_Nmove 0 3 left right head none

/-- Helper: in the `s0_continue` filtered block, find the entry for `v`
when `v ∈ {1,2,3,4}` (encoded as `v ≠ 0 ∧ v ≠ 5 ∧ v ≠ 6` and `v < sigSAT`). -/
private theorem find_s0_continue_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne0 : v ≠ 0) (h_ne5 : v ≠ 5) (h_ne6 : v ≠ 6)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter
          (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6))).map s0_continue_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_continue_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true ⟨h_ne0, h_ne5, h_ne6⟩
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_continue_entry w :: ws.map s0_continue_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 0, sym = `some v` with `v ∈ {1,2,3,4}`: advance right, stay in state 0. -/
theorem TM_step_continue
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne0 : v ≠ 0) (h_ne5 : v ≠ 5) (h_ne6 : v ≠ 6)
    (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne5 h2.symm
    simp [h_ne_some]
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hFind := find_s0_continue_match left right head v
    h_head_lt h_get h_ne0 h_ne5 h_ne6 h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hNot_s1_none,
      List.find?_append, List.find?_append, hFind]
  show applyTransitionEntry _ (s0_continue_entry v) = _
  exact applyEntry_Rmove 0 0 left right head (some v)

/-- Helper: every entry in `s0_continue` block fails to match state 0
when the symbol is in `{0, 6}` (because the filter excludes those). -/
private theorem find_s0_continue_none_for_reject
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 0 ∨ v = 6) :
    (((List.range sigSAT).filter
          (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6))).map s0_continue_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) = none := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  -- Every element w of the filtered list satisfies w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6.
  -- Since v ∈ {0, 6}, w ≠ v for every w in the list, so no entry matches.
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6)) = L
  have hL_props : ∀ w ∈ L, w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6 := by
    intro w hw
    have hw' : w ∈ (List.range sigSAT).filter
        (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6)) := hList ▸ hw
    exact of_decide_eq_true (List.mem_filter.mp hw').2
  clear hList
  induction L with
  | nil => rfl
  | cons w ws ih =>
      show List.find? _ (s0_continue_entry w :: ws.map s0_continue_entry) = _
      rw [List.find?_cons]
      have hw_props := hL_props w (List.mem_cons.mpr (Or.inl rfl))
      have hwv : w ≠ v := by
        rcases h_v_in with h0 | h6
        · subst h0; exact hw_props.1
        · subst h6; exact hw_props.2.2
      have hNotMatch : entryMatchesConfig (s0_continue_entry w)
          { state_idx := 0, tapes := [(left, head, right)] } = false := by
        show ((0 : Nat) == 0 &&
                decide (([some w] : List (Option Nat)) =
                  [currentTapeSymbol (left, head, right)])) = false
        rw [hSym]
        have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
          intro h; injection h with h1; injection h1 with h2; exact hwv h2
        simp [h_ne_some]
      rw [hNotMatch]
      exact ih (fun w' hw' => hL_props w' (List.mem_cons.mpr (Or.inr hw')))

/-- Helper: find s0_reject_symbol_entry v when v ∈ {0, 6}. -/
private theorem find_s0_reject_symbol_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 0 ∨ v = 6)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter
          (fun w => decide (w = 0 ∨ w = 6))).map s0_reject_symbol_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_reject_symbol_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w = 0 ∨ w = 6)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_v_in
  generalize hList : (List.range sigSAT).filter (fun w => decide (w = 0 ∨ w = 6)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_reject_symbol_entry w :: ws.map s0_reject_symbol_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_reject_symbol_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_reject_symbol_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 0, sym = `some v` with `v ∈ {0, 6}`: reject. -/
theorem TM_step_reject_s0_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 0 ∨ v = 6)
    (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have h_v_ne5 : v ≠ 5 := by
    rcases h_v_in with h | h <;> (subst h; decide)
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_v_ne5 h2.symm
    simp [h_ne_some]
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hContNone := find_s0_continue_none_for_reject left right head v
    h_head_lt h_get h_v_in
  have hRejFind := find_s0_reject_symbol_match left right head v
    h_head_lt h_get h_v_in h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hNot_s1_none,
      List.find?_append, List.find?_append, hContNone, Option.none_or, hRejFind]
  show applyTransitionEntry _ (s0_reject_symbol_entry v) = _
  exact applyEntry_Nmove 0 3 left right head (some v)

/-- State 1, sym = `some 0`: accept. -/
theorem TM_step_accept_0
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 0
    rw [dif_pos h_head_lt, h_get]
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hMatch : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_accept_entry = _
  exact applyEntry_Nmove 1 2 left right head (some 0)

/-- State 1, sym = `none`: reject. -/
theorem TM_step_reject_s1_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 0] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatch : entryMatchesConfig s1_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_reject_none_entry = _
  exact applyEntry_Nmove 1 3 left right head none

/-- Helper: every entry in `s0_continue` block fails to match state 1
(because src_state = 0). -/
private theorem find_s0_continue_none_for_s1
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6))).map s0_continue_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 1, tapes := [(left, head, right)] }) = none := by
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w ≠ 0 ∧ w ≠ 5 ∧ w ≠ 6)) = L
  clear hList
  induction L with
  | nil => rfl
  | cons w ws ih =>
      show List.find? _ (s0_continue_entry w :: ws.map s0_continue_entry) = _
      rw [List.find?_cons]
      have hNotMatch : entryMatchesConfig (s0_continue_entry w)
          { state_idx := 1, tapes := [(left, head, right)] } = false := by
        show ((0 : Nat) == 1 &&
                decide (([some w] : List (Option Nat)) =
                  [currentTapeSymbol (left, head, right)])) = false
        rfl
      rw [hNotMatch]
      exact ih

/-- Helper: every entry in `s0_reject_symbol` block fails to match state 1
(because src_state = 0). -/
private theorem find_s0_reject_none_for_s1
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun w => decide (w = 0 ∨ w = 6))).map s0_reject_symbol_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 1, tapes := [(left, head, right)] }) = none := by
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w = 0 ∨ w = 6)) = L
  clear hList
  induction L with
  | nil => rfl
  | cons w ws ih =>
      show List.find? _ (s0_reject_symbol_entry w :: ws.map s0_reject_symbol_entry) = _
      rw [List.find?_cons]
      have hNotMatch : entryMatchesConfig (s0_reject_symbol_entry w)
          { state_idx := 1, tapes := [(left, head, right)] } = false := by
        show ((0 : Nat) == 1 &&
                decide (([some w] : List (Option Nat)) =
                  [currentTapeSymbol (left, head, right)])) = false
        rfl
      rw [hNotMatch]
      exact ih

/-- Helper: find s1_reject_symbol_entry v when v ≠ 0. -/
private theorem find_s1_reject_symbol_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne0 : v ≠ 0) (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter
          (fun w => decide (w ≠ 0))).map s1_reject_symbol_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 1, tapes := [(left, head, right)] }) =
      some (s1_reject_symbol_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 0)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_ne0
  generalize hList : (List.range sigSAT).filter (fun w => decide (w ≠ 0)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s1_reject_symbol_entry w :: ws.map s1_reject_symbol_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s1_reject_symbol_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = true := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((1 : Nat) == 1) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s1_reject_symbol_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = false := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 1, sym = `some v` with `v ≠ 0`: reject. -/
theorem TM_step_reject_s1_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne0 : v ≠ 0) (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNot_advance : entryMatchesConfig s0_advance_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rfl
  have hNot_s1_acc : entryMatchesConfig s1_accept_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 0] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne0 h2.symm
    simp [h_ne_some]
  have hNot_s1_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hContNone := find_s0_continue_none_for_s1 left right head
  have hRejNone := find_s0_reject_none_for_s1 left right head
  have hS1Find := find_s1_reject_symbol_match left right head v
    h_head_lt h_get h_ne0 h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_advance,
      List.find?_cons, hNot_s0_none,
      List.find?_cons, hNot_s1_acc,
      List.find?_cons, hNot_s1_none,
      List.find?_append, List.find?_append, hContNone, Option.none_or,
      hRejNone, Option.none_or, hS1Find]
  show applyTransitionEntry _ (s1_reject_symbol_entry v) = _
  exact applyEntry_Nmove 1 3 left right head (some v)

/-! ### Inductive scan-loop: walk past the CNF encoding -/

/-- Unfold `runFlatTM (n+1)` at state 0 given a known one-step transition.
State 0 is non-halting (`halt[0] = false`), so the if-branch falls through. -/
private theorem runFlatTM_state0_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 0, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

/-- The scan-loop: starting at state 0 with head at position `head`, where
positions `head, head+1, …, head+gap-1` all carry symbols in `{1,2,3,4}`
and position `head+gap` carries `5`, after exactly `gap + 1` steps the
TM reaches state 1 with head advanced to `head + gap + 1`. -/
theorem TM_run_scan_to_5
    (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = 5 →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ ≠ 0 ∧
        right.get ⟨head + k, h⟩ ≠ 5 ∧
        right.get ⟨head + k, h⟩ ≠ 6 ∧
        right.get ⟨head + k, h⟩ < sigSAT) →
      runFlatTM (gap + 1) TM
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, head + gap + 1, right)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get_5 : right.get ⟨head, h_lt⟩ = 5 := by
        have := h_get_target
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [heq] at this
        exact this
      rw [runFlatTM_state0_unfold 0 left right head _
        (TM_step_advance_5 left right head h_lt h_get_5)]
      show (some { state_idx := 1, tapes := [(left, head + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + 0 + 1, right)] }
      rw [Nat.add_zero]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_ne0, h_ne5, h_ne6, h_lt⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_get_head_ne0 : right.get ⟨head, h_head_lt⟩ ≠ 0 := by
        rw [heq0] at h_ne0; exact h_ne0
      have h_get_head_ne5 : right.get ⟨head, h_head_lt⟩ ≠ 5 := by
        rw [heq0] at h_ne5; exact h_ne5
      have h_get_head_ne6 : right.get ⟨head, h_head_lt⟩ ≠ 6 := by
        rw [heq0] at h_ne6; exact h_ne6
      have h_get_head_lt : right.get ⟨head, h_head_lt⟩ < sigSAT := by
        rw [heq0] at h_lt; exact h_lt
      -- Step 1: advance.
      have h_step := TM_step_continue left right head
        (right.get ⟨head, h_head_lt⟩) h_head_lt rfl
        h_get_head_ne0 h_get_head_ne5 h_get_head_ne6 h_get_head_lt
      -- IH at head+1, gap.
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range' : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head + 1) + gap, h_in_range'⟩ = 5 := by
        have heq : (⟨(head + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < right.length),
            right.get ⟨(head + 1) + k, h⟩ ≠ 0 ∧
            right.get ⟨(head + 1) + k, h⟩ ≠ 5 ∧
            right.get ⟨(head + 1) + k, h⟩ ≠ 6 ∧
            right.get ⟨(head + 1) + k, h⟩ < sigSAT := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk', h1, h2, h3, h4⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk'' : (head + 1) + k < right.length := hShift ▸ h_kk'
        refine ⟨h_kk'', ?_, ?_, ?_, ?_⟩
        all_goals
          (have heq : (⟨(head + 1) + k, h_kk''⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk'⟩ := Fin.eq_of_val_eq hShift.symm
           rw [heq])
        · exact h1
        · exact h2
        · exact h3
        · exact h4
      have hih :=
        TM_run_scan_to_5 left right gap (head + 1) h_in_range' h_get_target' h_before'
      rw [runFlatTM_state0_unfold (gap + 1) left right head _ h_step]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (head + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + (gap + 1) + 1, right)] }
      rw [h_succ]
  termination_by gap _ _ _ _ => gap

/-! ### Encoding facts for `AssgnEmpty`

We need:
- The interior of `encodeCnf N` (all but the trailing `5`) is in `{1,2,3,4}`.
- The trailing symbol is `5`.
- Position `(encodeCnf N).length` of `encodeInput (N, a)` is `0` iff `a = []`.
- Length facts (the indices we use are in range). -/

theorem encodeLiteral_in_one_to_three (l : literal) :
    ∀ x ∈ encodeLiteral l, x = 1 ∨ x = 2 ∨ x = 3 := by
  rcases l with ⟨b, v⟩
  cases b
  · -- (false, v) → 3 :: List.replicate v 1
    intro x hx
    have hx' : x ∈ 3 :: List.replicate v 1 := hx
    rcases List.mem_cons.mp hx' with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (List.mem_replicate.mp h).2
  · -- (true, v) → 2 :: List.replicate v 1
    intro x hx
    have hx' : x ∈ 2 :: List.replicate v 1 := hx
    rcases List.mem_cons.mp hx' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (List.mem_replicate.mp h).2

theorem encodeClause_in_one_to_four (c : clause) :
    ∀ x ∈ encodeClause c, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  intro x hx
  unfold encodeClause at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_flatten.mp h with ⟨L, hL_in, hx_in_L⟩
    rcases List.mem_map.mp hL_in with ⟨l, _, hL_eq⟩
    rw [← hL_eq] at hx_in_L
    rcases encodeLiteral_in_one_to_three l x hx_in_L with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rw [List.mem_singleton.mp h]
    exact Or.inr (Or.inr (Or.inr rfl))

/-- Interior of `encodeCnf N` (the `flatten` part, before the trailing `5`) —
every symbol is in `{1, 2, 3, 4}`. -/
theorem encodeCnf_interior_in_one_to_four (N : cnf) :
    ∀ x ∈ (N.map encodeClause).flatten, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  intro x hx
  rcases List.mem_flatten.mp hx with ⟨L, hL_in, hx_in_L⟩
  rcases List.mem_map.mp hL_in with ⟨c, _, hL_eq⟩
  rw [← hL_eq] at hx_in_L
  exact encodeClause_in_one_to_four c x hx_in_L

/-- `encodeCnf N` is non-empty (always at least the trailing `5`). -/
theorem encodeCnf_length_pos (N : cnf) : 0 < (encodeCnf N).length := by
  show 0 < ((N.map encodeClause).flatten ++ [5]).length
  rw [List.length_append, List.length_singleton]
  exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_left _ _)

/-- `encodeCnf N` ends with `5`. -/
theorem encodeCnf_get_last (N : cnf)
    (h : (encodeCnf N).length - 1 < (encodeCnf N).length) :
    (encodeCnf N)[(encodeCnf N).length - 1]'h = 5 := by
  -- encodeCnf N = (N.map encodeClause).flatten ++ [5].
  have h_eq : encodeCnf N = (N.map encodeClause).flatten ++ [5] := rfl
  set interior := (N.map encodeClause).flatten with h_interior
  have h_len : (encodeCnf N).length = interior.length + 1 := by
    rw [h_eq, List.length_append, List.length_singleton]
  have h_idx_eq : (encodeCnf N).length - 1 = interior.length := by
    rw [h_len]; rfl
  -- After both rewrites, we have `(interior ++ [5])[interior.length]'h = 5`.
  rw [show (encodeCnf N)[(encodeCnf N).length - 1]'h =
        (interior ++ [5])[(encodeCnf N).length - 1]'(h_eq ▸ h) from rfl]
  rw [List.getElem_append_right (by rw [h_idx_eq])]
  simp [h_idx_eq]

/-- Positions before the last in `encodeCnf N` carry symbols in `{1,2,3,4}`. -/
theorem encodeCnf_get_interior (N : cnf) (k : Nat)
    (h_k_lt : k < (encodeCnf N).length - 1) :
    ∃ (h : k < (encodeCnf N).length),
      (encodeCnf N)[k]'h ≠ 0 ∧
      (encodeCnf N)[k]'h ≠ 5 ∧
      (encodeCnf N)[k]'h ≠ 6 ∧
      (encodeCnf N)[k]'h < sigSAT := by
  have h_eq : encodeCnf N = (N.map encodeClause).flatten ++ [5] := rfl
  set interior := (N.map encodeClause).flatten with h_interior
  have h_len : (encodeCnf N).length = interior.length + 1 := by
    rw [h_eq, List.length_append, List.length_singleton]
  have h_k_lt_int : k < interior.length := by
    have : (encodeCnf N).length - 1 = interior.length := by rw [h_len]; rfl
    rw [this] at h_k_lt; exact h_k_lt
  have h_k_lt_full : k < (encodeCnf N).length :=
    Nat.lt_of_lt_of_le h_k_lt_int (by rw [h_len]; exact Nat.le_succ _)
  have h_get_eq : (encodeCnf N)[k]'h_k_lt_full = interior[k]'h_k_lt_int := by
    show (interior ++ [5])[k]'(h_eq ▸ h_k_lt_full) = _
    exact List.getElem_append_left h_k_lt_int
  have h_mem : interior[k]'h_k_lt_int ∈ interior := List.getElem_mem h_k_lt_int
  have h_one_to_four := encodeCnf_interior_in_one_to_four N _ h_mem
  refine ⟨h_k_lt_full, ?_, ?_, ?_, ?_⟩
  · rw [h_get_eq]; rcases h_one_to_four with h | h | h | h <;> (rw [h]; decide)
  · rw [h_get_eq]; rcases h_one_to_four with h | h | h | h <;> (rw [h]; decide)
  · rw [h_get_eq]; rcases h_one_to_four with h | h | h | h <;> (rw [h]; decide)
  · rw [h_get_eq]; rcases h_one_to_four with h | h | h | h <;> (rw [h]; decide)

/-- For any position in the CNF part of the input, the symbol is the same
as in `encodeCnf N`. -/
theorem encodeInput_get_in_cnf (N : cnf) (a : assgn) (k : Nat)
    (h_k_cnf : k < (encodeCnf N).length) :
    (encodeInput (N, a))[k]'(by
      show k < (encodeCnf N ++ encodeAssgn a).length
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le h_k_cnf (Nat.le_add_right _ _)) =
      (encodeCnf N)[k]'h_k_cnf := by
  show (encodeCnf N ++ encodeAssgn a)[k]'_ = _
  exact List.getElem_append_left h_k_cnf

theorem encodeAssgn_length_pos : ∀ (a : assgn), 0 < (encodeAssgn a).length
  | [] => by show 0 < ([0] : List Nat).length; decide
  | v :: vs => by
      show 0 < (List.replicate v 1 ++ 6 :: encodeAssgn vs).length
      rw [List.length_append, List.length_replicate, List.length_cons]
      exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_left _ _)

/-- Length of the encoded input is at least `(encodeCnf N).length + 1`. -/
theorem encodeInput_length_gt_cnf (N : cnf) (a : assgn) :
    (encodeCnf N).length < (encodeInput (N, a)).length := by
  show (encodeCnf N).length < (encodeCnf N ++ encodeAssgn a).length
  rw [List.length_append]
  exact Nat.lt_add_of_pos_right (encodeAssgn_length_pos a)

/-- Position `(encodeCnf N).length` of the input = first symbol of the
assignment encoding. -/
theorem encodeInput_get_at_assgn_start (N : cnf) (a : assgn) :
    (encodeInput (N, a))[(encodeCnf N).length]'(encodeInput_length_gt_cnf N a) =
      (encodeAssgn a)[0]'(encodeAssgn_length_pos a) := by
  show (encodeCnf N ++ encodeAssgn a)[(encodeCnf N).length]'_ = _
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

theorem encodeAssgn_first_symbol_empty :
    (encodeAssgn ([] : assgn))[0]'(encodeAssgn_length_pos []) = 0 := rfl

theorem encodeAssgn_first_symbol_nonempty (v : Nat) (vs : assgn) :
    (encodeAssgn (v :: vs))[0]'(encodeAssgn_length_pos (v :: vs)) = 1 ∨
    (encodeAssgn (v :: vs))[0]'(encodeAssgn_length_pos (v :: vs)) = 6 := by
  cases v with
  | zero =>
      right
      show (([] : List Nat) ++ 6 :: encodeAssgn vs)[0]'_ = 6
      rfl
  | succ w =>
      left
      show (1 :: List.replicate w 1 ++ 6 :: encodeAssgn vs)[0]'_ = 1
      rfl

/-- Chaining lemma: an `n`-step run landing in a non-halting config can be
extended by a single explicit step. Generalisation of `runFlatTM_extend`. -/
theorem runFlatTM_extend_by_step
    (M : FlatTM) :
    ∀ (n : Nat) (cfg cfg_mid cfg_final : FlatTMConfig),
      runFlatTM n M cfg = some cfg_mid →
      haltingStateReached M cfg_mid = false →
      stepFlatTM M cfg_mid = some cfg_final →
      runFlatTM (n + 1) M cfg = some cfg_final
  | 0, cfg, cfg_mid, cfg_final, h_run, h_mid_not_halt, h_step => by
      -- runFlatTM 0 cfg = some cfg, so cfg = cfg_mid.
      have h_eq : cfg = cfg_mid := Option.some.inj h_run
      rw [h_eq]
      show (if haltingStateReached M cfg_mid = true then some cfg_mid
            else match stepFlatTM M cfg_mid with
              | none => some cfg_mid
              | some cfg' => runFlatTM 0 M cfg') = some cfg_final
      rw [if_neg (by rw [h_mid_not_halt]; decide), h_step]
      rfl
  | n + 1, cfg, cfg_mid, cfg_final, h_run, h_mid_not_halt, h_step => by
      have h_run_eq :
          runFlatTM (n + 1) M cfg =
            if haltingStateReached M cfg = true then some cfg
            else match stepFlatTM M cfg with
              | none => some cfg
              | some cfg' => runFlatTM n M cfg' := rfl
      by_cases h_cfg_halt : haltingStateReached M cfg = true
      · -- cfg halting → runFlatTM (n+1) cfg = some cfg = some cfg_mid, so cfg = cfg_mid.
        -- But cfg_mid is non-halting; contradiction.
        rw [h_run_eq, if_pos h_cfg_halt] at h_run
        have h_eq : cfg = cfg_mid := Option.some.inj h_run
        rw [h_eq] at h_cfg_halt
        rw [h_mid_not_halt] at h_cfg_halt
        exact absurd h_cfg_halt (by decide)
      · rw [h_run_eq, if_neg h_cfg_halt] at h_run
        cases h_step_cfg : stepFlatTM M cfg with
        | none =>
            rw [h_step_cfg] at h_run
            -- runFlatTM (n+1) cfg = some cfg = some cfg_mid → cfg = cfg_mid.
            -- Then stepFlatTM cfg_mid = none, but h_step says it's some cfg_final.
            have h_eq : cfg = cfg_mid := Option.some.inj h_run
            rw [h_eq] at h_step_cfg
            rw [h_step_cfg] at h_step
            cases h_step
        | some cfg' =>
            rw [h_step_cfg] at h_run
            -- runFlatTM n cfg' = some cfg_mid. Apply IH.
            have ih := runFlatTM_extend_by_step M n cfg' cfg_mid cfg_final
              h_run h_mid_not_halt h_step
            -- We want runFlatTM (n+2) cfg = some cfg_final.
            have h_run2_eq :
                runFlatTM (n + 1 + 1) M cfg =
                  if haltingStateReached M cfg = true then some cfg
                  else match stepFlatTM M cfg with
                    | none => some cfg
                    | some cfg' => runFlatTM (n + 1) M cfg' := rfl
            rw [h_run2_eq, if_neg h_cfg_halt, h_step_cfg]
            exact ih
  termination_by n _ _ _ _ _ _ => n

/-! ### The `AssgnEmpty` decider

The framework needed is now in place:

- `TM_run_scan_to_5` walks past the CNF interior to the `5` terminator.
- `TM_step_accept_0` / `TM_step_reject_s1_symbol` perform the final check.
- `runFlatTM_extend_by_step` chains a non-halting run with a single step.
- `runFlatTM_extend` pads a halting run to the uniform time budget.
- The encoding facts give the position of `5` and the start of the
  assignment in the encoded input.

Assembling these pieces into the full `DecidesBy` witness for
`AssgnEmpty` is mechanical but quite long; we defer it to the next
session along with `inTimePolyTM_assgnEmpty`. -/

/-- The complete scan-loop: starting at state 0 with head 0, after
`(encodeCnf N).length` steps the TM is in state 1 with head positioned
at the start of the assignment encoding. This is the reusable helper
used by both `decides_pos` and `decides_neg`. -/
private theorem run_scan_to_assgn_start (N : cnf) (a : assgn) :
    runFlatTM (encodeCnf N).length TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, a))] } =
      some { state_idx := 1,
             tapes := [([], (encodeCnf N).length, encodeInput (N, a))] } := by
  have h_cnf_pos := encodeCnf_length_pos N
  have h_input_len_gt := encodeInput_length_gt_cnf N a
  have h_5_in_cnf : (encodeCnf N).length - 1 < (encodeCnf N).length :=
    Nat.sub_lt h_cnf_pos (Nat.zero_lt_succ _)
  have h_gap_succ : (encodeCnf N).length - 1 + 1 = (encodeCnf N).length :=
    Nat.sub_add_cancel h_cnf_pos
  have h_5_in_range :
      0 + ((encodeCnf N).length - 1) < (encodeInput (N, a)).length := by
    rw [Nat.zero_add]; exact Nat.lt_trans h_5_in_cnf h_input_len_gt
  have h_5_in_input : (encodeCnf N).length - 1 < (encodeInput (N, a)).length :=
    Nat.lt_trans h_5_in_cnf h_input_len_gt
  have h_get_5 :
      (encodeInput (N, a)).get ⟨0 + ((encodeCnf N).length - 1), h_5_in_range⟩ = 5 := by
    have heq : (⟨0 + ((encodeCnf N).length - 1), h_5_in_range⟩ :
                 Fin (encodeInput (N, a)).length) =
        ⟨(encodeCnf N).length - 1, h_5_in_input⟩ :=
      Fin.eq_of_val_eq (Nat.zero_add _)
    rw [heq]
    show (encodeInput (N, a))[(encodeCnf N).length - 1]'h_5_in_input = 5
    rw [encodeInput_get_in_cnf N a ((encodeCnf N).length - 1) h_5_in_cnf]
    exact encodeCnf_get_last N h_5_in_cnf
  have h_before : ∀ k, k < (encodeCnf N).length - 1 →
      ∃ (h : 0 + k < (encodeInput (N, a)).length),
        (encodeInput (N, a)).get ⟨0 + k, h⟩ ≠ 0 ∧
        (encodeInput (N, a)).get ⟨0 + k, h⟩ ≠ 5 ∧
        (encodeInput (N, a)).get ⟨0 + k, h⟩ ≠ 6 ∧
        (encodeInput (N, a)).get ⟨0 + k, h⟩ < sigSAT := by
    intro k hk
    rcases encodeCnf_get_interior N k hk with ⟨h_k_cnf, h0, h5, h6, hlt⟩
    have h_k_input_zero : 0 + k < (encodeInput (N, a)).length := by
      rw [Nat.zero_add]; exact Nat.lt_trans h_k_cnf h_input_len_gt
    have h_k_input : k < (encodeInput (N, a)).length :=
      Nat.lt_trans h_k_cnf h_input_len_gt
    -- Convert Fin index ⟨0 + k, _⟩ to ⟨k, _⟩.
    have heq : (⟨0 + k, h_k_input_zero⟩ : Fin (encodeInput (N, a)).length) =
        ⟨k, h_k_input⟩ := Fin.eq_of_val_eq (Nat.zero_add k)
    have h_get_eq : (encodeInput (N, a)).get ⟨0 + k, h_k_input_zero⟩ =
        (encodeCnf N)[k]'h_k_cnf := by
      rw [heq]
      show (encodeInput (N, a))[k]'h_k_input = (encodeCnf N)[k]'h_k_cnf
      exact encodeInput_get_in_cnf N a k h_k_cnf
    refine ⟨h_k_input_zero, ?_, ?_, ?_, ?_⟩
    · rw [h_get_eq]; exact h0
    · rw [h_get_eq]; exact h5
    · rw [h_get_eq]; exact h6
    · rw [h_get_eq]; exact hlt
  have h_scan_run := TM_run_scan_to_5 [] (encodeInput (N, a))
    ((encodeCnf N).length - 1) 0 h_5_in_range h_get_5 h_before
  -- h_scan_run : runFlatTM ((encodeCnf N).length - 1 + 1) TM cfg_0 =
  --   some { state_idx := 1, tapes := [([], 0 + ((encodeCnf N).length - 1) + 1, ...)] }
  -- Normalize via h_gap_succ and Nat.zero_add.
  have h_idx_eq : 0 + ((encodeCnf N).length - 1) + 1 = (encodeCnf N).length := by
    rw [Nat.zero_add]; exact h_gap_succ
  rw [h_idx_eq] at h_scan_run
  rw [h_gap_succ] at h_scan_run
  exact h_scan_run

/-- `(encodeCnf N).length ≤ encodable.size (N, a) + 1`. Used to pad the
decider's actual time `(encodeCnf N).length + 1` to the uniform budget
`encodable.size + 2`. -/
private theorem encodeCnf_length_le (N : cnf) (a : assgn) :
    (encodeCnf N).length ≤ encodable.size (N, a) + 1 := by
  have h_cnf_le_input : (encodeCnf N).length ≤ (encodeInput (N, a)).length := by
    show (encodeCnf N).length ≤ (encodeCnf N ++ encodeAssgn a).length
    rw [List.length_append]; exact Nat.le_add_right _ _
  exact Nat.le_trans h_cnf_le_input (encodeInput_length_le N a)

theorem timeBound_inOPoly : inOPoly (fun n : Nat => n + 2) :=
  inOPoly_add inOPoly_id (inOPoly_const 2)

theorem timeBound_monotonic : monotonic (fun n : Nat => n + 2) := by
  intro a b h
  exact Nat.add_le_add_right h 2

/-- The TM-backed decider for "the assignment is empty". -/
def decider : DecidesBy
    (fun Na : cnf × assgn => Na.2 = [])
    (fun n => n + 2) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 2
  rejectState := 3
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ ha
    subst ha
    -- Scan past the CNF (state 0 → state 1), then accept on the `0` terminator.
    have h_scan := run_scan_to_assgn_start N []
    have h_assgn_pos : (encodeCnf N).length < (encodeInput (N, [])).length :=
      encodeInput_length_gt_cnf N []
    have h_get_assgn : (encodeInput (N, [])).get
        ⟨(encodeCnf N).length, h_assgn_pos⟩ = 0 := by
      show (encodeInput (N, []))[(encodeCnf N).length]'h_assgn_pos = 0
      rw [encodeInput_get_at_assgn_start N []]
      exact encodeAssgn_first_symbol_empty
    have h_step_accept :=
      TM_step_accept_0 [] (encodeInput (N, [])) (encodeCnf N).length
        h_assgn_pos h_get_assgn
    have h_mid_not_halt :
        haltingStateReached TM
          { state_idx := 1,
            tapes := [([], (encodeCnf N).length, encodeInput (N, []))] } = false := rfl
    have h_chain := runFlatTM_extend_by_step TM (encodeCnf N).length _ _ _
      h_scan h_mid_not_halt h_step_accept
    -- h_chain : runFlatTM ((encodeCnf N).length + 1) TM cfg_0 = some cfg_final
    have h_final_halt :
        haltingStateReached TM
          { state_idx := 2,
            tapes := [([], (encodeCnf N).length, encodeInput (N, []))] } = true := rfl
    -- Pad to encodable.size (N, []) + 2.
    have h_le : (encodeCnf N).length + 1 ≤ encodable.size (N, ([] : assgn)) + 2 := by
      have := encodeCnf_length_le N ([] : assgn)
      exact Nat.add_le_add_right this 1
    rcases Nat.le.dest h_le with ⟨k, h_k⟩
    have h_padded : runFlatTM ((encodeCnf N).length + 1 + k) TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, []))] } =
        some { state_idx := 2,
               tapes := [([], (encodeCnf N).length, encodeInput (N, []))] } :=
      TMPrimitives.runFlatTM_extend h_chain h_final_halt
    rw [h_k] at h_padded
    -- h_padded : runFlatTM (encodable.size (N, []) + 2) ... = some { state := 2, ... }
    refine ⟨_, ?_, h_final_halt, rfl⟩
    show runFlatTM (encodable.size (N, ([] : assgn)) + 2) TM
        (initFlatConfig TM (initialTapes TM (encodeInput (N, [])))) = _
    show runFlatTM (encodable.size (N, ([] : assgn)) + 2) TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, []))] } = _
    exact h_padded
  decides_neg := by
    rintro ⟨N, a⟩ ha
    -- a ≠ [], so a = v :: vs.
    cases a with
    | nil => exact absurd rfl ha
    | cons v vs =>
        -- Scan past the CNF. Then read the first assgn symbol (1 or 6), reject.
        have h_scan := run_scan_to_assgn_start N (v :: vs)
        have h_assgn_pos : (encodeCnf N).length < (encodeInput (N, v :: vs)).length :=
          encodeInput_length_gt_cnf N (v :: vs)
        -- First assignment symbol is 1 (if v ≥ 1) or 6 (if v = 0).
        have h_first_sym :
            (encodeInput (N, v :: vs))[(encodeCnf N).length]'h_assgn_pos = 1 ∨
            (encodeInput (N, v :: vs))[(encodeCnf N).length]'h_assgn_pos = 6 := by
          rw [encodeInput_get_at_assgn_start N (v :: vs)]
          exact encodeAssgn_first_symbol_nonempty v vs
        -- Build the rejecting step.
        rcases h_first_sym with h1 | h6
        · -- v ≥ 1: symbol is 1.
          have h_get_assgn :
              (encodeInput (N, v :: vs)).get
                ⟨(encodeCnf N).length, h_assgn_pos⟩ = 1 := h1
          have h_step_reject := TM_step_reject_s1_symbol []
            (encodeInput (N, v :: vs)) (encodeCnf N).length 1
            h_assgn_pos h_get_assgn (by decide) (by decide)
          have h_mid_not_halt :
              haltingStateReached TM
                { state_idx := 1,
                  tapes := [([], (encodeCnf N).length, encodeInput (N, v :: vs))] } =
                false := rfl
          have h_chain := runFlatTM_extend_by_step TM (encodeCnf N).length _ _ _
            h_scan h_mid_not_halt h_step_reject
          have h_final_halt :
              haltingStateReached TM
                { state_idx := 3,
                  tapes := [([], (encodeCnf N).length, encodeInput (N, v :: vs))] } =
                true := rfl
          have h_le :
              (encodeCnf N).length + 1 ≤ encodable.size (N, v :: vs) + 2 := by
            exact Nat.add_le_add_right (encodeCnf_length_le N (v :: vs)) 1
          rcases Nat.le.dest h_le with ⟨k, h_k⟩
          have h_padded :=
            TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
          rw [h_k] at h_padded
          refine ⟨_, ?_, h_final_halt, rfl⟩
          show runFlatTM (encodable.size (N, v :: vs) + 2) TM
              (initFlatConfig TM
                (initialTapes TM (encodeInput (N, v :: vs)))) = _
          show runFlatTM (encodable.size (N, v :: vs) + 2) TM
              { state_idx := 0, tapes := [([], 0, encodeInput (N, v :: vs))] } = _
          exact h_padded
        · -- v = 0: symbol is 6.
          have h_get_assgn :
              (encodeInput (N, v :: vs)).get
                ⟨(encodeCnf N).length, h_assgn_pos⟩ = 6 := h6
          have h_step_reject := TM_step_reject_s1_symbol []
            (encodeInput (N, v :: vs)) (encodeCnf N).length 6
            h_assgn_pos h_get_assgn (by decide) (by decide)
          have h_mid_not_halt :
              haltingStateReached TM
                { state_idx := 1,
                  tapes := [([], (encodeCnf N).length, encodeInput (N, v :: vs))] } =
                false := rfl
          have h_chain := runFlatTM_extend_by_step TM (encodeCnf N).length _ _ _
            h_scan h_mid_not_halt h_step_reject
          have h_final_halt :
              haltingStateReached TM
                { state_idx := 3,
                  tapes := [([], (encodeCnf N).length, encodeInput (N, v :: vs))] } =
                true := rfl
          have h_le :
              (encodeCnf N).length + 1 ≤ encodable.size (N, v :: vs) + 2 := by
            exact Nat.add_le_add_right (encodeCnf_length_le N (v :: vs)) 1
          rcases Nat.le.dest h_le with ⟨k, h_k⟩
          have h_padded :=
            TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
          rw [h_k] at h_padded
          refine ⟨_, ?_, h_final_halt, rfl⟩
          show runFlatTM (encodable.size (N, v :: vs) + 2) TM
              (initFlatConfig TM
                (initialTapes TM (encodeInput (N, v :: vs)))) = _
          show runFlatTM (encodable.size (N, v :: vs) + 2) TM
              { state_idx := 0, tapes := [([], 0, encodeInput (N, v :: vs))] } = _
          exact h_padded

/-- "The assignment is empty" is in TM-backed polynomial time. -/
theorem inTimePolyTM_assgnEmpty :
    inTimePolyTM (fun Na : cnf × assgn => Na.2 = []) :=
  ⟨fun n => n + 2, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end AssgnEmpty

/-! ## `CnfStartsEmpty`: a 1-step decider for "the first clause is empty"

The predicate is `Na.1.head? = some []`, i.e. the CNF is non-empty and
its first clause has no literals.

In our encoding, `encodeCnf ([] :: rest) = 4 :: …`, while
`encodeCnf [] = 5 :: …` and `encodeCnf ((ℓ :: ls) :: rest)` starts with a
sign byte `2` or `3`. So the predicate reduces to **"position 0 of the
encoded input is `4`"** — a 1-step single-symbol read, identical in shape
to `CnfEmpty.TM` but with accept symbol `4` instead of `5`. -/

namespace CnfStartsEmpty

/-- The 3-state TM. State 0 reads position 0; state 1 is accept-halt;
state 2 is reject-halt. -/
def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 3
  trans :=
    let mkAccept : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some 4]
        dst_state := 1
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let mkRejectSymbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [some v]
        dst_state := 2
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    let mkRejectNone : FlatTMTransEntry :=
      { src_state := 0
        src_tape_vals := [none]
        dst_state := 2
        dst_write_vals := [none]
        move_dirs := [TMMove.Nmove] }
    mkAccept :: mkRejectNone ::
      ((List.range sigSAT).filter (fun v => decide (v ≠ 4))).map mkRejectSymbol
  start := 0
  halt := [false, true, true]

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 3; decide
  · show [false, true, true].length = 3; rfl
  · intro entry hentry
    have hentry' : entry ∈ TM.trans := hentry
    show flatTMTransEntryValid TM entry
    unfold TM at hentry'
    rcases List.mem_cons.mp hentry' with hAccept | hRest
    · subst hAccept
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 3; decide
      · show 1 < 3; decide
      · intro x hx
        simp at hx
        subst hx
        show 4 < sigSAT; decide
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_cons.mp hRest with hNone | hRej
      · subst hNone
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp at hx; subst hx; trivial
        · intro x hx; simp at hx; subst hx; trivial
      · rcases List.mem_map.mp hRej with ⟨v, hv, hmk⟩
        subst hmk
        have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp at hx; subst hx; exact hvlt
        · intro x hx; simp at hx; subst hx; trivial

/-! ### First-symbol facts for `CnfStartsEmpty`

We need to characterize the symbol at position 0 of `encodeInput (N, a)`:

- For `N = [] :: rest` (the head is the empty clause), it is `4`.
- For `N = []`, it is `5`.
- For `N = (ℓ :: ls) :: rest`, it is `2` or `3`. -/

theorem encodeInput_starts_empty_clause_head (rest : cnf) (a : assgn) :
    (encodeInput (([] : clause) :: rest, a)).head? = some 4 := rfl

theorem encodeInput_empty_cnf_head_ne_4 (a : assgn) :
    (encodeInput ([], a)).head? ≠ some 4 := by
  show (encodeCnf [] ++ encodeAssgn a).head? ≠ some 4
  show ((([] : cnf).map encodeClause).flatten ++ [5] ++ encodeAssgn a).head? ≠ some 4
  rw [List.map_nil, List.flatten_nil, List.nil_append]
  intro h
  cases a
  · injection h with h1; exact absurd h1 (by decide)
  · injection h with h1; exact absurd h1 (by decide)

theorem encodeInput_cons_literal_head_ne_4 (l : literal) (ls : clause) (rest : cnf)
    (a : assgn) : (encodeInput ((l :: ls) :: rest, a)).head? ≠ some 4 := by
  rcases l with ⟨b, v⟩
  cases b
  · have h_head : (encodeInput (((false, v) :: ls) :: rest, a)).head? = some 3 := rfl
    rw [h_head]
    intro h; injection h with h1; exact absurd h1 (by decide)
  · have h_head : (encodeInput (((true, v) :: ls) :: rest, a)).head? = some 2 := rfl
    rw [h_head]
    intro h; injection h with h1; exact absurd h1 (by decide)

/-! ### Operational correctness for `CnfStartsEmpty.TM` -/

private def acceptEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 4]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def rejectNoneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def rejectSymbolEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans = acceptEntry :: rejectNoneEntry ::
      ((List.range sigSAT).filter (fun v => decide (v ≠ 4))).map rejectSymbolEntry := rfl

private theorem applyEntry_singleTape
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

theorem TM_step_match
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 4) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 4 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 4
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ acceptEntry = _
  exact applyEntry_singleTape 0 1 left right head (some 4)

theorem TM_step_reject_none
    (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = none := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
    rw [dif_neg h_head_ge]
  have hNotMatchAcc : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 4] : List (Option Nat)) ≠ [none] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hMatchNone : entryMatchesConfig rejectNoneEntry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNotMatchAcc, List.find?_cons, hMatchNone]
  show applyTransitionEntry _ rejectNoneEntry = _
  exact applyEntry_singleTape 0 2 left right head none

private theorem find_rejectSymbolEntry_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_ne : v ≠ 4)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter (fun w => decide (w ≠ 4))).map rejectSymbolEntry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }) =
      some (rejectSymbolEntry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w ≠ 4)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_ne
  generalize hList : (List.range sigSAT).filter (fun w => decide (w ≠ 4)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (rejectSymbolEntry w :: ws.map rejectSymbolEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (rejectSymbolEntry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (rejectSymbolEntry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h
            injection h with h1
            injection h1 with h2
            exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

theorem TM_step_reject_symbol
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_ne : v ≠ 4)
    (h_v_lt : v < sigSAT) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNotMatchAcc : entryMatchesConfig acceptEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([some 4] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1
      injection h1 with h2
      exact h_ne h2.symm
    simp [h_ne_some]
  have hNotMatchNone : entryMatchesConfig rejectNoneEntry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne_some : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne_some]
  have hFind := find_rejectSymbolEntry_match left right head v h_head_lt h_get h_ne h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNotMatchAcc, List.find?_cons, hNotMatchNone, hFind]
  show applyTransitionEntry _ (rejectSymbolEntry v) = _
  exact applyEntry_singleTape 0 2 left right head (some v)

private theorem run_one (left right : List Nat) (head : Nat) (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM 1 TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg' := by
  show (if haltingStateReached TM
            { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM 0 TM cfg'') = some cfg'
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

/-- The TM-backed decider for "the first clause of the CNF in the input is
empty (and the CNF is non-empty)". -/
def decider : DecidesBy
    (fun Na : cnf × assgn => Na.1.head? = some [])
    (fun _ => 1) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 1
  rejectState := 2
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ hN_head
    -- Na.1.head? = some [] ⇒ N = [] :: rest.
    cases N with
    | nil =>
        -- head? = none, contradicts hN_head : head? = some []
        exact absurd hN_head (by simp [List.head?])
    | cons C rest =>
        -- head? (C :: rest) = some C, so C = [].
        have hC : C = ([] : clause) := by
          have : (C :: rest).head? = some C := rfl
          rw [this] at hN_head
          injection hN_head
        subst hC
        -- encodeInput (([]) :: rest, a) starts with 4.
        have h_head_lt : (0 : Nat) < (encodeInput (([] : clause) :: rest, a)).length := by
          show 0 < (4 :: ((rest.map encodeClause).flatten ++ [5] ++ encodeAssgn a)).length
          exact Nat.zero_lt_succ _
        have h_get : (encodeInput (([] : clause) :: rest, a)).get ⟨0, h_head_lt⟩ = 4 := rfl
        have h_step :=
          TM_step_match [] (encodeInput (([] : clause) :: rest, a)) 0 h_head_lt h_get
        have h_run := run_one [] (encodeInput (([] : clause) :: rest, a)) 0
          { state_idx := 1, tapes := [([], 0, encodeInput (([] : clause) :: rest, a))] } h_step
        exact ⟨_, h_run, rfl, rfl⟩
  decides_neg := by
    rintro ⟨N, a⟩ hN_head
    cases N with
    | nil =>
        -- encodeInput ([], a) = 5 :: …
        have h_head_lt : (0 : Nat) < (encodeInput ([], a)).length := by
          show 0 < (5 :: encodeAssgn a).length
          exact Nat.zero_lt_succ _
        have h_get : (encodeInput ([], a)).get ⟨0, h_head_lt⟩ = 5 := rfl
        have h_step := TM_step_reject_symbol []
          (encodeInput ([], a)) 0 5 h_head_lt h_get
          (by decide) (by decide)
        have h_run := run_one [] (encodeInput ([], a)) 0 _ h_step
        exact ⟨_, h_run, rfl, rfl⟩
    | cons C rest =>
        -- head? = some C; hN_head says some C ≠ some []. So C ≠ [].
        have hC_ne : C ≠ ([] : clause) := by
          intro hC; apply hN_head
          have : (C :: rest).head? = some C := rfl
          rw [this, hC]
        cases C with
        | nil => exact absurd rfl hC_ne
        | cons l ls =>
            rcases l with ⟨b, v⟩
            cases b
            · have h_head_lt :
                  (0 : Nat) < (encodeInput (((false, v) :: ls) :: rest, a)).length := by
                show 0 < (3 :: _).length
                exact Nat.zero_lt_succ _
              have h_get :
                  (encodeInput (((false, v) :: ls) :: rest, a)).get ⟨0, h_head_lt⟩ = 3 := rfl
              have h_step := TM_step_reject_symbol []
                (encodeInput (((false, v) :: ls) :: rest, a)) 0 3 h_head_lt h_get
                (by decide) (by decide)
              have h_run :=
                run_one [] (encodeInput (((false, v) :: ls) :: rest, a)) 0 _ h_step
              exact ⟨_, h_run, rfl, rfl⟩
            · have h_head_lt :
                  (0 : Nat) < (encodeInput (((true, v) :: ls) :: rest, a)).length := by
                show 0 < (2 :: _).length
                exact Nat.zero_lt_succ _
              have h_get :
                  (encodeInput (((true, v) :: ls) :: rest, a)).get ⟨0, h_head_lt⟩ = 2 := rfl
              have h_step := TM_step_reject_symbol []
                (encodeInput (((true, v) :: ls) :: rest, a)) 0 2 h_head_lt h_get
                (by decide) (by decide)
              have h_run :=
                run_one [] (encodeInput (((true, v) :: ls) :: rest, a)) 0 _ h_step
              exact ⟨_, h_run, rfl, rfl⟩

theorem timeBound_inOPoly : inOPoly (fun _ : Nat => 1) :=
  inOPoly_const 1

theorem timeBound_monotonic : monotonic (fun _ : Nat => 1) := fun _ _ _ => Nat.le_refl 1

/-- "The CNF starts with an empty clause" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfStartsEmpty :
    inTimePolyTM (fun Na : cnf × assgn => Na.1.head? = some []) :=
  ⟨fun _ => 1, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end CnfStartsEmpty

/-! ## `CnfNonempty` and `AssgnNonempty`: negation combinator examples

A decider for `P` is automatically a decider for `¬ P` after swapping
`acceptState` and `rejectState` — `DecidesBy.negate` (in `TMDecider.lean`)
packages this fact. We use it here to derive deciders for `Na.1 ≠ []` and
`Na.2 ≠ []` for free, without writing any new TM. -/

namespace CnfNonempty

/-- The decider for `Na.1 ≠ []`, obtained by negating `CnfEmpty.decider`. -/
noncomputable def decider :
    DecidesBy (fun Na : cnf × assgn => Na.1 ≠ []) (fun _ => 1) :=
  CnfEmpty.decider.negate

/-- "The CNF is non-empty" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfNonempty :
    inTimePolyTM (fun Na : cnf × assgn => Na.1 ≠ []) :=
  inTimePolyTM_not CnfEmpty.inTimePolyTM_cnfEmpty

end CnfNonempty

namespace AssgnNonempty

/-- The decider for `Na.2 ≠ []`, obtained by negating `AssgnEmpty.decider`. -/
noncomputable def decider :
    DecidesBy (fun Na : cnf × assgn => Na.2 ≠ []) (fun n => n + 2) :=
  AssgnEmpty.decider.negate

/-- "The assignment is non-empty" is in TM-backed polynomial time. -/
theorem inTimePolyTM_assgnNonempty :
    inTimePolyTM (fun Na : cnf × assgn => Na.2 ≠ []) :=
  inTimePolyTM_not AssgnEmpty.inTimePolyTM_assgnEmpty

end AssgnNonempty

/-! ## `.iff`-derived deciders

The `DecidesBy.iff` combinator lets us repackage an existing decider's
predicate into an equivalent Lean spelling at zero TM cost. These three
examples illustrate the pattern. -/

/-- `Na.1 ≠ [] ↔ ∃ c rest, Na.1 = c :: rest`. -/
theorem cnf_nonempty_iff_cons (Na : cnf × assgn) :
    Na.1 ≠ [] ↔ ∃ c rest, Na.1 = c :: rest := by
  constructor
  · intro h
    rcases hN : Na.1 with _ | ⟨c, rest⟩
    · exact absurd hN h
    · exact ⟨c, rest, rfl⟩
  · rintro ⟨c, rest, hEq⟩ hNil
    rw [hEq] at hNil
    exact List.cons_ne_nil c rest hNil

/-- "The CNF can be written as `c :: rest`" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfCons :
    inTimePolyTM (fun Na : cnf × assgn => ∃ c rest, Na.1 = c :: rest) :=
  inTimePolyTM_iff cnf_nonempty_iff_cons CnfNonempty.inTimePolyTM_cnfNonempty

/-- `Na.2 ≠ [] ↔ ∃ v rest, Na.2 = v :: rest`. -/
theorem assgn_nonempty_iff_cons (Na : cnf × assgn) :
    Na.2 ≠ [] ↔ ∃ v rest, Na.2 = v :: rest := by
  constructor
  · intro h
    rcases hA : Na.2 with _ | ⟨v, rest⟩
    · exact absurd hA h
    · exact ⟨v, rest, rfl⟩
  · rintro ⟨v, rest, hEq⟩ hNil
    rw [hEq] at hNil
    exact List.cons_ne_nil v rest hNil

/-- "The assignment can be written as `v :: rest`" is in TM-backed polynomial time. -/
theorem inTimePolyTM_assgnCons :
    inTimePolyTM (fun Na : cnf × assgn => ∃ v rest, Na.2 = v :: rest) :=
  inTimePolyTM_iff assgn_nonempty_iff_cons AssgnNonempty.inTimePolyTM_assgnNonempty

/-- `Na.1 = [] ↔ Na.1.length = 0`. -/
theorem cnf_empty_iff_length_zero (Na : cnf × assgn) :
    Na.1 = [] ↔ Na.1.length = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact List.length_eq_zero_iff.mp h

/-- "The CNF has length 0" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfLengthZero :
    inTimePolyTM (fun Na : cnf × assgn => Na.1.length = 0) :=
  inTimePolyTM_iff cnf_empty_iff_length_zero CnfEmpty.inTimePolyTM_cnfEmpty

/-- The negation of `CnfEmptyAssgnEmpty`: at least one of the CNF or
assignment is non-empty. Decided in 2 steps. -/
theorem inTimePolyTM_cnfOrAssgnNonempty :
    inTimePolyTM (fun Na : cnf × assgn => ¬ (Na.1 = [] ∧ Na.2 = [])) :=
  inTimePolyTM_not CnfEmptyAssgnEmpty.inTimePolyTM_cnfEmptyAssgnEmpty

/-- `¬ (Na.1 = [] ∧ Na.2 = []) ↔ Na.1 ≠ [] ∨ Na.2 ≠ []`. -/
theorem not_both_empty_iff (Na : cnf × assgn) :
    (¬ (Na.1 = [] ∧ Na.2 = [])) ↔ (Na.1 ≠ [] ∨ Na.2 ≠ []) := by
  constructor
  · intro h
    by_cases hN : Na.1 = []
    · by_cases hA : Na.2 = []
      · exact absurd ⟨hN, hA⟩ h
      · exact Or.inr hA
    · exact Or.inl hN
  · rintro (hN | hA) ⟨h1, h2⟩
    · exact hN h1
    · exact hA h2

/-- "The CNF is non-empty OR the assignment is non-empty" is in
TM-backed polynomial time. -/
theorem inTimePolyTM_cnfOrAssgnNonempty' :
    inTimePolyTM (fun Na : cnf × assgn => Na.1 ≠ [] ∨ Na.2 ≠ []) :=
  inTimePolyTM_iff not_both_empty_iff inTimePolyTM_cnfOrAssgnNonempty

/-! ## `CnfHasEmptyClause`: a 4-state CNF walker

The predicate is `∃ c ∈ Na.1, c = []` — the CNF contains an empty
clause (a structural unsatisfiability witness; an empty clause has no
literal that can satisfy it).

This is the **first multi-state walker** in the project: it
alternates between state 0 ("at clause start") and state 1 ("in a
non-empty clause"), driven by the symbol under the head:

- State 0, see `4`: empty clause found → accept (state 2).
- State 0, see `5`: end of CNF, no empty clause → reject (state 3).
- State 0, see sign byte `2`/`3`: enter literal → state 1, advance.
- State 1, see `4`: clause finished, all non-empty so far → state 0,
  advance to next clause.
- State 1, see digit/sign `1`/`2`/`3`: continue in clause → state 1,
  advance.
- State 1, see `5`: end of CNF mid-clause → reject.
- All other symbols / `none` in either state → reject.

This is the prototype for the outer loop of `evalCnfTM`. -/

namespace CnfHasEmptyClause

def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 4
  trans :=
    let s0_accept_4 : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some 4], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_reject_5 : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some 5], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_reject_none : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [none], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_advance_4 : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 4], dst_state := 0,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s1_reject_5 : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 5], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_reject_none : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [none], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_enter (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_other (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_continue (v : Nat) : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some v], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s1_reject_other (v : Nat) : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some v], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    s0_accept_4 :: s0_reject_5 :: s0_reject_none ::
    s1_advance_4 :: s1_reject_5 :: s1_reject_none ::
      (((List.range sigSAT).filter (fun v => decide (v = 2 ∨ v = 3))).map s0_enter ++
        ((List.range sigSAT).filter (fun v => decide (v = 0 ∨ v = 1 ∨ v = 6))).map s0_reject_other ++
        ((List.range sigSAT).filter (fun v => decide (v = 1 ∨ v = 2 ∨ v = 3))).map s1_continue ++
        ((List.range sigSAT).filter (fun v => decide (v = 0 ∨ v = 6))).map s1_reject_other)
  start := 0
  halt := [false, false, true, true]

private def s0_accept_4_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 4], dst_state := 2,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_reject_5_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 5], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_reject_none_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [none], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_advance_4_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 4], dst_state := 0,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s1_reject_5_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 5], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_reject_none_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [none], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_enter_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_other_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_continue_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some v], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s1_reject_other_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some v], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans =
      s0_accept_4_entry :: s0_reject_5_entry :: s0_reject_none_entry ::
      s1_advance_4_entry :: s1_reject_5_entry :: s1_reject_none_entry ::
      (((List.range sigSAT).filter (fun v => decide (v = 2 ∨ v = 3))).map s0_enter_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 1 ∨ v = 6))).map s0_reject_other_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 1 ∨ v = 2 ∨ v = 3))).map s1_continue_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 6))).map s1_reject_other_entry) := rfl

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 4; decide
  · show [false, false, true, true].length = 4; rfl
  · intro entry hentry
    show flatTMTransEntryValid TM entry
    rw [TM_trans_eq] at hentry
    -- 6 fixed entries followed by ((s0_enter ++ s0_reject_other) ++ s1_continue) ++ s1_reject_other.
    rcases List.mem_cons.mp hentry with h | h1
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 4; decide
      · show 2 < 4; decide
      · intro x hx
        have hx' : x ∈ ([some 4] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 4 < sigSAT; decide
      · intro x hx
        have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    · rcases List.mem_cons.mp h1 with h | h2
      · subst h
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 4; decide
        · show 3 < 4; decide
        · intro x hx
          have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; show 5 < sigSAT; decide
        · intro x hx
          have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; trivial
      · rcases List.mem_cons.mp h2 with h | h3
        · subst h
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 0 < 4; decide
          · show 3 < 4; decide
          · intro x hx
            have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; trivial
          · intro x hx
            have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; trivial
        · rcases List.mem_cons.mp h3 with h | h4
          · subst h
            refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
            · show 1 < 4; decide
            · show 0 < 4; decide
            · intro x hx
              have hx' : x ∈ ([some 4] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'; subst hx'; show 4 < sigSAT; decide
            · intro x hx
              have hx' : x ∈ ([none] : List (Option Nat)) := hx
              rw [List.mem_singleton] at hx'; subst hx'; trivial
          · rcases List.mem_cons.mp h4 with h | h5
            · subst h
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 1 < 4; decide
              · show 3 < 4; decide
              · intro x hx
                have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'; subst hx'; show 5 < sigSAT; decide
              · intro x hx
                have hx' : x ∈ ([none] : List (Option Nat)) := hx
                rw [List.mem_singleton] at hx'; subst hx'; trivial
            · rcases List.mem_cons.mp h5 with h | h6
              · subst h
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 1 < 4; decide
                · show 3 < 4; decide
                · intro x hx
                  have hx' : x ∈ ([none] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; trivial
                · intro x hx
                  have hx' : x ∈ ([none] : List (Option Nat)) := hx
                  rw [List.mem_singleton] at hx'; subst hx'; trivial
              · -- filtered block: ((s0_enter ++ s0_reject_other) ++ s1_continue) ++ s1_reject_other
                rcases List.mem_append.mp h6 with hLeft3 | hS1Rej
                · rcases List.mem_append.mp hLeft3 with hLeft2 | hS1Cont
                  · rcases List.mem_append.mp hLeft2 with hEnter | hS0Rej
                    · -- s0_enter from filter (v ∈ {2, 3})
                      rcases List.mem_map.mp hEnter with ⟨v, hv, hmk⟩
                      subst hmk
                      have hvlt : v < sigSAT :=
                        List.mem_range.mp (List.mem_filter.mp hv).1
                      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                      · show 0 < 4; decide
                      · show 1 < 4; decide
                      · intro x hx
                        have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                        rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                      · intro x hx
                        have hx' : x ∈ ([none] : List (Option Nat)) := hx
                        rw [List.mem_singleton] at hx'; subst hx'; trivial
                    · -- s0_reject_other from filter (v ∈ {0, 1, 6})
                      rcases List.mem_map.mp hS0Rej with ⟨v, hv, hmk⟩
                      subst hmk
                      have hvlt : v < sigSAT :=
                        List.mem_range.mp (List.mem_filter.mp hv).1
                      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                      · show 0 < 4; decide
                      · show 3 < 4; decide
                      · intro x hx
                        have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                        rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                      · intro x hx
                        have hx' : x ∈ ([none] : List (Option Nat)) := hx
                        rw [List.mem_singleton] at hx'; subst hx'; trivial
                  · -- s1_continue from filter (v ∈ {1, 2, 3})
                    rcases List.mem_map.mp hS1Cont with ⟨v, hv, hmk⟩
                    subst hmk
                    have hvlt : v < sigSAT :=
                      List.mem_range.mp (List.mem_filter.mp hv).1
                    refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                    · show 1 < 4; decide
                    · show 1 < 4; decide
                    · intro x hx
                      have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                      rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                    · intro x hx
                      have hx' : x ∈ ([none] : List (Option Nat)) := hx
                      rw [List.mem_singleton] at hx'; subst hx'; trivial
                · -- s1_reject_other from filter (v ∈ {0, 6})
                  rcases List.mem_map.mp hS1Rej with ⟨v, hv, hmk⟩
                  subst hmk
                  have hvlt : v < sigSAT :=
                    List.mem_range.mp (List.mem_filter.mp hv).1
                  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                  · show 1 < 4; decide
                  · show 3 < 4; decide
                  · intro x hx
                    have hx' : x ∈ ([some v] : List (Option Nat)) := hx
                    rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
                  · intro x hx
                    have hx' : x ∈ ([none] : List (Option Nat)) := hx
                    rw [List.mem_singleton] at hx'; subst hx'; trivial

/-! ### Single-tape `applyTransitionEntry` for our shape -/

private theorem applyEntry_Nmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

private theorem applyEntry_Rmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Rmove] } =
      some { state_idx := new_state, tapes := [(left, head + 1, right)] } := rfl

/-! ### Step lemmas: state 0 -/

/-- From state 0, reading `4` → state 2 (accept), head unchanged. -/
theorem TM_step_s0_accept_4
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 4) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 4 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 4
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s0_accept_4_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_accept_4_entry = _
  exact applyEntry_Nmove 0 2 left right head (some 4)

/-- From state 0, reading `5` → state 3 (reject), head unchanged. -/
theorem TM_step_s0_reject_5
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hNot_s0_accept_4 : entryMatchesConfig s0_accept_4_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 4] : List (Option Nat)) ≠ [some 5] := by
      intro h; injection h with h1; injection h1 with h2; exact absurd h2 (by decide)
    simp [h_ne]
  have hMatch : entryMatchesConfig s0_reject_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hNot_s0_accept_4, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_reject_5_entry = _
  exact applyEntry_Nmove 0 3 left right head (some 5)

/-- Helper: in state 0, the head symbol `some v` for `v ∈ {2, 3}` makes
`s0_enter v` the first match in the filtered s0_enter block. -/
private theorem find_s0_enter_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_v : v = 2 ∨ v = 3)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter
        (fun w => decide (w = 2 ∨ w = 3))).map s0_enter_entry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_enter_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w = 2 ∨ w = 3)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_v
  generalize hList : (List.range sigSAT).filter (fun w => decide (w = 2 ∨ w = 3)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_enter_entry w :: ws.map s0_enter_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_enter_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_enter_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- From state 0, reading a sign byte (`2` or `3`) → state 1, head
advances. -/
theorem TM_step_s0_enter
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_v : v = 2 ∨ v = 3) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have h_v_lt : v < sigSAT := by
    rcases h_v with h | h
    · rw [h]; decide
    · rw [h]; decide
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  -- None of the 6 fixed entries match (state 0, symbol v with v ∈ {2, 3}, none of {4, 5}).
  have hNot_s0_accept_4 : entryMatchesConfig s0_accept_4_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 4] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2
      rcases h_v with h | h <;> (rw [h] at h2; exact absurd h2 (by decide))
    simp [h_ne]
  have hNot_s0_reject_5 : entryMatchesConfig s0_reject_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2
      rcases h_v with h | h <;> (rw [h] at h2; exact absurd h2 (by decide))
    simp [h_ne]
  have hNot_s0_reject_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hNot_s1_advance_4 : entryMatchesConfig s1_advance_4_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 0 && _) = false
    rfl
  have hNot_s1_reject_5 : entryMatchesConfig s1_reject_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  have hNot_s1_reject_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  have hFind := find_s0_enter_match left right head v h_head_lt h_get h_v h_v_lt
  -- After skipping all 6 fixed entries, we look at the filtered block which is the appended
  -- left-associative ((s0_enter ++ s0_reject_other) ++ s1_continue) ++ s1_reject_other.
  -- The s0_enter block comes first (leftmost), so List.find? hits it.
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, hNot_s0_accept_4, List.find?_cons, hNot_s0_reject_5,
      List.find?_cons, hNot_s0_reject_none, List.find?_cons, hNot_s1_advance_4,
      List.find?_cons, hNot_s1_reject_5, List.find?_cons, hNot_s1_reject_none]
  -- Now we're looking at: List.find? (((A ++ B) ++ C) ++ D)
  rw [List.find?_append, List.find?_append, List.find?_append, hFind]
  show applyTransitionEntry _ (s0_enter_entry v) = _
  exact applyEntry_Rmove 0 1 left right head (some v)

/-! ### Step lemmas: state 1 -/

/-- From state 1, reading `4` → state 0 (next clause), head advances. -/
theorem TM_step_s1_advance_4
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 4) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 4 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 4
    rw [dif_pos h_head_lt, h_get]
  -- Entries 1-3 are state 0, so don't match in state 1.
  have hNot_s0_accept_4 : entryMatchesConfig s0_accept_4_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hNot_s0_reject_5 : entryMatchesConfig s0_reject_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hNot_s0_reject_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hMatch : entryMatchesConfig s1_advance_4_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, hNot_s0_accept_4, List.find?_cons, hNot_s0_reject_5,
      List.find?_cons, hNot_s0_reject_none, List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_advance_4_entry = _
  exact applyEntry_Rmove 1 0 left right head (some 4)

/-- Helper: in state 1, head symbol `some v` for `v ∈ {1, 2, 3}` makes
`s1_continue v` the first match in the s1_continue block. -/
private theorem find_s1_continue_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_v : v = 1 ∨ v = 2 ∨ v = 3)
    (h_v_lt : v < sigSAT) :
    (((List.range sigSAT).filter
        (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3))).map s1_continue_entry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }) =
      some (s1_continue_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_v
  generalize hList : (List.range sigSAT).filter (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s1_continue_entry w :: ws.map s1_continue_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s1_continue_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = true := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((1 : Nat) == 1) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s1_continue_entry w)
            { state_idx := 1, tapes := [(left, head, right)] } = false := by
          show ((1 : Nat) == 1 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- Skip helper: when in state 1, the s0_enter block contains only
state-0 entries, none of which match. -/
private theorem find_s0_enter_skip_for_s1
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
        (fun w => decide (w = 2 ∨ w = 3))).map s0_enter_entry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }) = none := by
  generalize (List.range sigSAT).filter (fun w => decide (w = 2 ∨ w = 3)) = L
  induction L with
  | nil => rfl
  | cons w ws ih =>
      show List.find? _ (s0_enter_entry w :: ws.map s0_enter_entry) = _
      rw [List.find?_cons]
      have hNotMatch : entryMatchesConfig (s0_enter_entry w)
          { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
      rw [hNotMatch]; exact ih

private theorem find_s0_reject_other_skip_for_s1
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
        (fun w => decide (w = 0 ∨ w = 1 ∨ w = 6))).map s0_reject_other_entry).find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }) = none := by
  generalize (List.range sigSAT).filter (fun w => decide (w = 0 ∨ w = 1 ∨ w = 6)) = L
  induction L with
  | nil => rfl
  | cons w ws ih =>
      show List.find? _ (s0_reject_other_entry w :: ws.map s0_reject_other_entry) = _
      rw [List.find?_cons]
      have hNotMatch : entryMatchesConfig (s0_reject_other_entry w)
          { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
      rw [hNotMatch]; exact ih

/-- From state 1, reading `1`/`2`/`3` → state 1, head advances. -/
theorem TM_step_s1_continue
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v) (h_v : v = 1 ∨ v = 2 ∨ v = 3) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have h_v_lt : v < sigSAT := by
    rcases h_v with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have hNot_s0_accept_4 : entryMatchesConfig s0_accept_4_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hNot_s0_reject_5 : entryMatchesConfig s0_reject_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hNot_s0_reject_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  have hNot_s1_advance_4 : entryMatchesConfig s1_advance_4_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 4] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 4] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2
      rcases h_v with h | h | h <;> (rw [h] at h2; exact absurd h2 (by decide))
    simp [h_ne]
  have hNot_s1_reject_5 : entryMatchesConfig s1_reject_5_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2
      rcases h_v with h | h | h <;> (rw [h] at h2; exact absurd h2 (by decide))
    simp [h_ne]
  have hNot_s1_reject_none : entryMatchesConfig s1_reject_none_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  have hSkipEnter := find_s0_enter_skip_for_s1 left right head
  have hSkipS0Rej := find_s0_reject_other_skip_for_s1 left right head
  have hFind := find_s1_continue_match left right head v h_head_lt h_get h_v h_v_lt
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, hNot_s0_accept_4, List.find?_cons, hNot_s0_reject_5,
      List.find?_cons, hNot_s0_reject_none, List.find?_cons, hNot_s1_advance_4,
      List.find?_cons, hNot_s1_reject_5, List.find?_cons, hNot_s1_reject_none]
  -- Now: List.find? (((A ++ B) ++ C) ++ D)
  rw [List.find?_append, List.find?_append, List.find?_append]
  rw [hSkipEnter, Option.none_or, hSkipS0Rej, Option.none_or, hFind]
  show applyTransitionEntry _ (s1_continue_entry v) = _
  exact applyEntry_Rmove 1 1 left right head (some v)

/-! ### Inductive scan lemma

State 1 is non-halting. The scan-loop from state 1 walks past `gap`
symbols in `{1, 2, 3}` and then through one `4`, reaching state 0
advanced by `gap + 1` positions. Parallel to `AssgnEmpty.TM_run_scan_to_5`. -/

private theorem runFlatTM_state1_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 1, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 1, tapes := [(left, head, right)] } = true then
          some { state_idx := 1, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } with
          | none => some { state_idx := 1, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

private theorem runFlatTM_state0_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 0, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

/-- The state-1 scan loop: starting at state 1 with head at `head`, walking
through `gap` symbols in `{1, 2, 3}` and then one `4`, lands in state 0
after `gap + 1` steps. -/
theorem TM_run_state1_to_4
    (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = 4 →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ = 1 ∨
        right.get ⟨head + k, h⟩ = 2 ∨
        right.get ⟨head + k, h⟩ = 3) →
      runFlatTM (gap + 1) TM
          { state_idx := 1, tapes := [(left, head, right)] } =
        some { state_idx := 0, tapes := [(left, head + gap + 1, right)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get_4 : right.get ⟨head, h_lt⟩ = 4 := by
        have := h_get_target
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [heq] at this
        exact this
      rw [runFlatTM_state1_unfold 0 left right head _
        (TM_step_s1_advance_4 left right head h_lt h_get_4)]
      show (some { state_idx := 0, tapes := [(left, head + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 0, tapes := [(left, head + 0 + 1, right)] }
      rw [Nat.add_zero]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_v⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_v' : right.get ⟨head, h_head_lt⟩ = 1 ∨ right.get ⟨head, h_head_lt⟩ = 2 ∨
          right.get ⟨head, h_head_lt⟩ = 3 := by
        rw [heq0] at h_v; exact h_v
      have h_step := TM_step_s1_continue left right head
        (right.get ⟨head, h_head_lt⟩) h_head_lt rfl h_v'
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range' : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head + 1) + gap, h_in_range'⟩ = 4 := by
        have heq : (⟨(head + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < right.length),
            right.get ⟨(head + 1) + k, h⟩ = 1 ∨
            right.get ⟨(head + 1) + k, h⟩ = 2 ∨
            right.get ⟨(head + 1) + k, h⟩ = 3 := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk', h_vk⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk'' : (head + 1) + k < right.length := hShift ▸ h_kk'
        refine ⟨h_kk'', ?_⟩
        have heq : (⟨(head + 1) + k, h_kk''⟩ : Fin right.length) =
            ⟨head + (k + 1), h_kk'⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h_vk
      have hih := TM_run_state1_to_4 left right gap (head + 1)
        h_in_range' h_get_target' h_before'
      rw [runFlatTM_state1_unfold (gap + 1) left right head _ h_step]
      rw [hih]
      show (some { state_idx := 0, tapes := [(left, (head + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 0, tapes := [(left, head + (gap + 1) + 1, right)] }
      rw [h_succ]
  termination_by gap _ _ _ _ => gap

/-! ### Encoding lemmas for `encodeClause`

We need positional facts:
- For non-empty `c`, position 0 is a sign byte (`2` or `3`).
- For any `c`, the last position is `4`.
- Every position before the last is in `{1, 2, 3}`.
- For non-empty `c`, the encoded length is ≥ 2. -/

theorem encodeClause_length_ge_two_nonempty (c : clause) (h_c_ne : c ≠ []) :
    2 ≤ (encodeClause c).length := by
  rcases c with _ | ⟨⟨b, v⟩, ls⟩
  · exact absurd rfl h_c_ne
  · show 2 ≤ (((((b, v) : literal) :: ls).map encodeLiteral).flatten ++ [4]).length
    rw [List.length_append, List.length_singleton]
    cases b
    · show 2 ≤ ((3 :: List.replicate v 1) ++ (ls.map encodeLiteral).flatten).length + 1
      rw [List.length_append, List.length_cons]
      omega
    · show 2 ≤ ((2 :: List.replicate v 1) ++ (ls.map encodeLiteral).flatten).length + 1
      rw [List.length_append, List.length_cons]
      omega

theorem encodeClause_get_zero_nonempty (c : clause) (h_c_ne : c ≠ []) :
    ∃ (h : 0 < (encodeClause c).length),
      (encodeClause c).get ⟨0, h⟩ = 2 ∨ (encodeClause c).get ⟨0, h⟩ = 3 := by
  rcases c with _ | ⟨⟨b, v⟩, ls⟩
  · exact absurd rfl h_c_ne
  · cases b
    · -- (false, v) :: ls: encodeClause starts with 3.
      have h : 0 < (encodeClause ((⟨false, v⟩ : literal) :: ls)).length := by
        have := encodeClause_length_ge_two_nonempty ((⟨false, v⟩ : literal) :: ls)
          (List.cons_ne_nil _ _)
        exact Nat.lt_of_lt_of_le (by decide) this
      refine ⟨h, ?_⟩
      show (encodeClause (((false, v) : literal) :: ls)).get ⟨0, h⟩ = 2 ∨ _ = 3
      right
      show (((((false, v) : literal) :: ls).map encodeLiteral).flatten ++ [4]).get ⟨0, h⟩ = 3
      rfl
    · have h : 0 < (encodeClause ((⟨true, v⟩ : literal) :: ls)).length := by
        have := encodeClause_length_ge_two_nonempty ((⟨true, v⟩ : literal) :: ls)
          (List.cons_ne_nil _ _)
        exact Nat.lt_of_lt_of_le (by decide) this
      refine ⟨h, ?_⟩
      show (encodeClause (((true, v) : literal) :: ls)).get ⟨0, h⟩ = 2 ∨ _ = 3
      left
      show (((((true, v) : literal) :: ls).map encodeLiteral).flatten ++ [4]).get ⟨0, h⟩ = 2
      rfl

theorem encodeClause_length_pos (c : clause) : 0 < (encodeClause c).length := by
  show 0 < ((c.map encodeLiteral).flatten ++ [4]).length
  rw [List.length_append, List.length_singleton]
  exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_add_left _ _)

theorem encodeClause_get_last_is_4 (c : clause)
    (h : (encodeClause c).length - 1 < (encodeClause c).length) :
    (encodeClause c).get ⟨(encodeClause c).length - 1, h⟩ = 4 := by
  have h_eq : encodeClause c = (c.map encodeLiteral).flatten ++ [4] := rfl
  set interior := (c.map encodeLiteral).flatten with h_interior
  have h_len : (encodeClause c).length = interior.length + 1 := by
    rw [h_eq, List.length_append, List.length_singleton]
  have h_idx_eq : (encodeClause c).length - 1 = interior.length := by
    rw [h_len]; rfl
  rw [show (encodeClause c).get ⟨(encodeClause c).length - 1, h⟩ =
        (interior ++ [4]).get ⟨(encodeClause c).length - 1, h_eq ▸ h⟩ from rfl]
  show (interior ++ [4])[(encodeClause c).length - 1]'(h_eq ▸ h) = 4
  rw [List.getElem_append_right (by rw [h_idx_eq])]
  simp [h_idx_eq]

theorem encodeClause_get_interior (c : clause) (k : Nat)
    (h_k_lt : k < (encodeClause c).length - 1) :
    ∃ (h : k < (encodeClause c).length),
      (encodeClause c).get ⟨k, h⟩ = 1 ∨
      (encodeClause c).get ⟨k, h⟩ = 2 ∨
      (encodeClause c).get ⟨k, h⟩ = 3 := by
  have h_eq : encodeClause c = (c.map encodeLiteral).flatten ++ [4] := rfl
  have h_len : (encodeClause c).length = (c.map encodeLiteral).flatten.length + 1 := by
    rw [h_eq, List.length_append, List.length_singleton]
  have h_k_lt_int : k < (c.map encodeLiteral).flatten.length := by
    have h_sub : (encodeClause c).length - 1 = (c.map encodeLiteral).flatten.length := by
      rw [h_len]; rfl
    rw [h_sub] at h_k_lt; exact h_k_lt
  have h_k_lt_full : k < (encodeClause c).length :=
    Nat.lt_of_lt_of_le h_k_lt_int (by rw [h_len]; exact Nat.le_succ _)
  have h_get_eq : (encodeClause c).get ⟨k, h_k_lt_full⟩ =
      (c.map encodeLiteral).flatten.get ⟨k, h_k_lt_int⟩ := by
    show ((c.map encodeLiteral).flatten ++ [4])[k]'(h_eq ▸ h_k_lt_full) = _
    exact List.getElem_append_left h_k_lt_int
  have h_mem : (c.map encodeLiteral).flatten.get ⟨k, h_k_lt_int⟩ ∈
      (c.map encodeLiteral).flatten := List.getElem_mem h_k_lt_int
  rcases List.mem_flatten.mp h_mem with ⟨L', hL_in, hx_in_L⟩
  rcases List.mem_map.mp hL_in with ⟨l, _, hL_eq⟩
  rw [← hL_eq] at hx_in_L
  have h_one_to_three := AssgnEmpty.encodeLiteral_in_one_to_three l _ hx_in_L
  refine ⟨h_k_lt_full, ?_⟩
  rw [h_get_eq]
  rcases h_one_to_three with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-! ### General composition lemma for `runFlatTM`

If `runFlatTM n M cfg = some cfg_mid`, then running for `n + m` steps
gives the same result as running for `m` more steps from `cfg_mid`. -/

theorem runFlatTM_stuck (M : FlatTM) (cfg : FlatTMConfig)
    (h_not_halt : haltingStateReached M cfg = false)
    (h_step : stepFlatTM M cfg = none) :
    ∀ (m : Nat), runFlatTM m M cfg = some cfg
  | 0 => rfl
  | m + 1 => by
      show (if haltingStateReached M cfg = true then some cfg
            else match stepFlatTM M cfg with
              | none => some cfg
              | some cfg' => runFlatTM m M cfg') = some cfg
      rw [if_neg (by rw [h_not_halt]; decide), h_step]

theorem runFlatTM_compose (M : FlatTM) :
    ∀ (n m : Nat) (cfg cfg_mid : FlatTMConfig),
      runFlatTM n M cfg = some cfg_mid →
      runFlatTM (n + m) M cfg = runFlatTM m M cfg_mid
  | 0, m, cfg, cfg_mid, h => by
      have h_eq : cfg = cfg_mid := by
        have : runFlatTM 0 M cfg = some cfg := rfl
        rw [this] at h; exact Option.some.inj h
      rw [h_eq, Nat.zero_add]
  | n + 1, m, cfg, cfg_mid, h => by
      by_cases h_halt : haltingStateReached M cfg = true
      · -- cfg halting: runFlatTM (n+1) cfg = some cfg, so cfg_mid = cfg.
        have h_run_eq : runFlatTM (n + 1) M cfg = some cfg := by
          show (if haltingStateReached M cfg = true then some cfg else _) = some cfg
          rw [if_pos h_halt]
        rw [h_run_eq] at h
        have h_eq : cfg = cfg_mid := Option.some.inj h
        rw [← h_eq]
        rw [runFlatTM_of_halting M cfg (n + 1 + m) h_halt,
            runFlatTM_of_halting M cfg m h_halt]
      · have h_halt' : haltingStateReached M cfg = false := by
          cases h_v : haltingStateReached M cfg with
          | true => exact absurd h_v h_halt
          | false => rfl
        cases h_step : stepFlatTM M cfg with
        | none =>
            -- step = none: runFlatTM (n+1) cfg = some cfg.
            have h_run_eq : runFlatTM (n + 1) M cfg = some cfg := by
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM n M cfg') = some cfg
              rw [if_neg h_halt, h_step]
            rw [h_run_eq] at h
            have h_eq : cfg = cfg_mid := Option.some.inj h
            rw [← h_eq]
            rw [runFlatTM_stuck M cfg h_halt' h_step (n + 1 + m),
                runFlatTM_stuck M cfg h_halt' h_step m]
        | some cfg' =>
            -- runFlatTM (n+1) cfg = runFlatTM n cfg'.
            have h_run_eq : runFlatTM (n + 1) M cfg = runFlatTM n M cfg' := by
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM n M cfg') = _
              rw [if_neg h_halt, h_step]
            rw [h_run_eq] at h
            -- By IH on n: runFlatTM (n + m) cfg' = runFlatTM m cfg_mid.
            have ih := runFlatTM_compose M n m cfg' cfg_mid h
            have h_run_full : runFlatTM (n + 1 + m) M cfg = runFlatTM (n + m) M cfg' := by
              have h_swap : n + 1 + m = n + m + 1 := by ring
              rw [h_swap]
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM (n + m) M cfg') = _
              rw [if_neg h_halt, h_step]
            rw [h_run_full, ih]
  termination_by n _ _ _ _ => n

/-! ### Walking past one non-empty clause -/

/-- Walk one non-empty clause from state 0: starting at position `p` with
the tape containing `encodeClause c` at positions `p, p+1, …`, after
`(encodeClause c).length` steps we return to state 0 at position
`p + (encodeClause c).length`. -/
private theorem TM_run_walk_one_clause (c : clause) (h_c_ne : c ≠ [])
    (left right : List Nat) (p : Nat)
    (h_match : ∀ k (h_k : k < (encodeClause c).length),
      ∃ (h : p + k < right.length),
        right.get ⟨p + k, h⟩ = (encodeClause c).get ⟨k, h_k⟩) :
    runFlatTM (encodeClause c).length TM
        { state_idx := 0, tapes := [(left, p, right)] } =
      some { state_idx := 0, tapes := [(left, p + (encodeClause c).length, right)] } := by
  have h_len_ge_two : 2 ≤ (encodeClause c).length :=
    encodeClause_length_ge_two_nonempty c h_c_ne
  have h_len_pos : 0 < (encodeClause c).length := encodeClause_length_pos c
  set L := (encodeClause c).length with hL
  -- Step 1: read pos p (sign byte), enter state 1, head p+1.
  rcases encodeClause_get_zero_nonempty c h_c_ne with ⟨h_zero_in, h_zero_v⟩
  rcases h_match 0 h_zero_in with ⟨h_p_lt, h_p_get⟩
  have h_p_lt' : p < right.length := by
    have := h_p_lt; rwa [Nat.add_zero] at this
  have h_p_get' : right.get ⟨p, h_p_lt'⟩ = 2 ∨ right.get ⟨p, h_p_lt'⟩ = 3 := by
    have heq : (⟨p + 0, h_p_lt⟩ : Fin right.length) = ⟨p, h_p_lt'⟩ :=
      Fin.eq_of_val_eq (Nat.add_zero p)
    rw [heq] at h_p_get
    rw [h_p_get]
    exact h_zero_v
  have h_step1 : stepFlatTM TM { state_idx := 0, tapes := [(left, p, right)] } =
      some { state_idx := 1, tapes := [(left, p + 1, right)] } :=
    TM_step_s0_enter left right p (right.get ⟨p, h_p_lt'⟩) h_p_lt' rfl h_p_get'
  -- Phase 2: run TM_run_state1_to_4 with gap = L - 2.
  have h_last_in : L - 1 < L := by
    rw [hL]; exact Nat.sub_lt h_len_pos (Nat.zero_lt_succ 0)
  rcases h_match (L - 1) (hL ▸ h_last_in) with ⟨h_last_lt, h_last_get⟩
  have h_last_target : right.get ⟨p + (L - 1), h_last_lt⟩ = 4 := by
    rw [h_last_get]
    show (encodeClause c).get ⟨(encodeClause c).length - 1, h_last_in⟩ = 4
    exact encodeClause_get_last_is_4 c h_last_in
  have h_shift_last : (p + 1) + (L - 2) = p + (L - 1) := by omega
  have h_in_range : (p + 1) + (L - 2) < right.length := by
    rw [h_shift_last]; exact h_last_lt
  have h_get_target :
      right.get ⟨(p + 1) + (L - 2), h_in_range⟩ = 4 := by
    have heq : (⟨(p + 1) + (L - 2), h_in_range⟩ : Fin right.length) =
        ⟨p + (L - 1), h_last_lt⟩ := Fin.eq_of_val_eq h_shift_last
    rw [heq]; exact h_last_target
  have h_before :
      ∀ k, k < L - 2 → ∃ (h : (p + 1) + k < right.length),
        right.get ⟨(p + 1) + k, h⟩ = 1 ∨
        right.get ⟨(p + 1) + k, h⟩ = 2 ∨
        right.get ⟨(p + 1) + k, h⟩ = 3 := by
    intro k hk
    have hk_lt : k + 1 < (encodeClause c).length - 1 := by rw [← hL]; omega
    rcases encodeClause_get_interior c (k + 1) hk_lt with ⟨h_k1_in, h_k1_v⟩
    rcases h_match (k + 1) h_k1_in with ⟨h_p_k1_lt, h_p_k1_get⟩
    have h_shift : (p + 1) + k = p + (k + 1) := by ring
    have h_p1_k_lt : (p + 1) + k < right.length := h_shift ▸ h_p_k1_lt
    refine ⟨h_p1_k_lt, ?_⟩
    have heq : (⟨(p + 1) + k, h_p1_k_lt⟩ : Fin right.length) =
        ⟨p + (k + 1), h_p_k1_lt⟩ := Fin.eq_of_val_eq h_shift
    rw [heq]; rw [h_p_k1_get]; exact h_k1_v
  have h_scan_run :=
    TM_run_state1_to_4 left right (L - 2) (p + 1) h_in_range h_get_target h_before
  -- Now compose: runFlatTM L TM cfg_0 = runFlatTM (L - 1) TM cfg_1 = some cfg_final.
  have h_L_eq : L = (L - 1) + 1 := by omega
  rw [h_L_eq]
  rw [runFlatTM_state0_unfold (L - 1) left right p _ h_step1]
  have h_L_minus_1_eq : L - 1 = (L - 2) + 1 := by omega
  rw [h_L_minus_1_eq]
  rw [h_scan_run]
  -- Need: (p + 1) + (L - 2) + 1 = p + (L - 2 + 1 + 1).
  have h_pos_eq : (p + 1) + (L - 2) + 1 = p + (L - 2 + 1 + 1) := by omega
  rw [h_pos_eq]

/-! ### Walking past a list of non-empty clauses

By induction on `cs`: walk through one clause, then recurse. Composed via
`runFlatTM_compose`. -/

private theorem TM_run_walk_clauses :
    ∀ (cs : cnf), (∀ c ∈ cs, c ≠ []) →
    ∀ (left right : List Nat) (p : Nat),
      (∀ k (h_k : k < (cs.map encodeClause).flatten.length),
        ∃ (h : p + k < right.length),
          right.get ⟨p + k, h⟩ = ((cs.map encodeClause).flatten).get ⟨k, h_k⟩) →
      runFlatTM ((cs.map encodeClause).flatten.length) TM
          { state_idx := 0, tapes := [(left, p, right)] } =
        some { state_idx := 0,
               tapes := [(left, p + (cs.map encodeClause).flatten.length, right)] }
  | [], _, left, right, p, _ => by
      show runFlatTM 0 TM
          { state_idx := 0, tapes := [(left, p, right)] } = _
      show (some { state_idx := 0, tapes := [(left, p, right)] } : Option FlatTMConfig) =
        some { state_idx := 0,
               tapes := [(left, p + ([].map encodeClause).flatten.length, right)] }
      have h_zero : (([] : cnf).map encodeClause).flatten.length = 0 := rfl
      rw [h_zero, Nat.add_zero]
  | c :: cs', h_all, left, right, p, h_match => by
      have h_c_ne : c ≠ [] := h_all c (List.mem_cons.mpr (Or.inl rfl))
      have h_cs'_ne : ∀ c' ∈ cs', c' ≠ [] := fun c' hc' =>
        h_all c' (List.mem_cons.mpr (Or.inr hc'))
      have h_split : ((c :: cs').map encodeClause).flatten =
          encodeClause c ++ (cs'.map encodeClause).flatten := rfl
      have h_len_split : ((c :: cs').map encodeClause).flatten.length =
          (encodeClause c).length + (cs'.map encodeClause).flatten.length := by
        rw [h_split, List.length_append]
      -- Build h_match_c (tape matches encodeClause c at positions p..)
      have h_match_c : ∀ k (h_k : k < (encodeClause c).length),
          ∃ (h : p + k < right.length),
            right.get ⟨p + k, h⟩ = (encodeClause c).get ⟨k, h_k⟩ := by
        intro k h_k
        have h_k_in_full : k < ((c :: cs').map encodeClause).flatten.length := by
          rw [h_len_split]; exact Nat.lt_of_lt_of_le h_k (Nat.le_add_right _ _)
        rcases h_match k h_k_in_full with ⟨h_p_lt, h_p_get⟩
        refine ⟨h_p_lt, ?_⟩
        rw [h_p_get]
        show (encodeClause c ++ (cs'.map encodeClause).flatten)[k]'h_k_in_full =
          (encodeClause c).get ⟨k, h_k⟩
        exact List.getElem_append_left h_k
      -- Step 1: walk c.
      have h_walk_c := TM_run_walk_one_clause c h_c_ne left right p h_match_c
      -- Build h_match_cs' (tape matches (cs'.map ec).flatten at positions p+ec.length..)
      have h_match_cs' : ∀ k (h_k : k < (cs'.map encodeClause).flatten.length),
          ∃ (h : (p + (encodeClause c).length) + k < right.length),
            right.get ⟨(p + (encodeClause c).length) + k, h⟩ =
              ((cs'.map encodeClause).flatten).get ⟨k, h_k⟩ := by
        intro k h_k
        have h_k' : (encodeClause c).length + k <
            ((c :: cs').map encodeClause).flatten.length := by
          rw [h_len_split]; exact Nat.add_lt_add_left h_k _
        have h_shift_idx : p + ((encodeClause c).length + k) =
            (p + (encodeClause c).length) + k := by ring
        rcases h_match ((encodeClause c).length + k) h_k' with ⟨h_p_lt, h_p_get⟩
        have h_pk_lt : (p + (encodeClause c).length) + k < right.length := by
          rw [← h_shift_idx]; exact h_p_lt
        refine ⟨h_pk_lt, ?_⟩
        have heq_idx : (⟨(p + (encodeClause c).length) + k, h_pk_lt⟩ : Fin right.length) =
            ⟨p + ((encodeClause c).length + k), h_p_lt⟩ := Fin.eq_of_val_eq h_shift_idx.symm
        rw [heq_idx, h_p_get]
        show (encodeClause c ++ (cs'.map encodeClause).flatten)[
              (encodeClause c).length + k]'h_k' = _
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp
      have ih := TM_run_walk_clauses cs' h_cs'_ne left right (p + (encodeClause c).length)
        h_match_cs'
      -- Compose.
      rw [h_len_split]
      have h_compose := runFlatTM_compose TM (encodeClause c).length
        (cs'.map encodeClause).flatten.length _ _ h_walk_c
      rw [h_compose]
      rw [ih]
      have h_assoc : p + (encodeClause c).length + (cs'.map encodeClause).flatten.length =
          p + ((encodeClause c).length + (cs'.map encodeClause).flatten.length) := by ring
      rw [h_assoc]
  termination_by cs _ _ _ _ _ => cs.length

/-! ### First-empty-clause split

If `N` has an empty clause, split `N = N₁ ++ [] :: N₂` where every clause
in `N₁` is non-empty (it's the prefix before the leftmost empty clause). -/

private theorem first_empty_clause_split (N : cnf) (h : ∃ c ∈ N, c = []) :
    ∃ N₁ N₂ : cnf, N = N₁ ++ [] :: N₂ ∧ ∀ c ∈ N₁, c ≠ [] := by
  induction N with
  | nil => rcases h with ⟨c, hc_in, _⟩; cases hc_in
  | cons c rest ih =>
      by_cases hc : c = []
      · refine ⟨[], rest, ?_, ?_⟩
        · subst hc; rfl
        · intro c' hc'; cases hc'
      · have h_rest : ∃ c' ∈ rest, c' = [] := by
          rcases h with ⟨c'', hc''_in, hc''_eq⟩
          rcases List.mem_cons.mp hc''_in with h1 | h2
          · exact absurd (h1 ▸ hc''_eq) hc
          · exact ⟨c'', h2, hc''_eq⟩
        rcases ih h_rest with ⟨N₁', N₂, hN, h_all⟩
        refine ⟨c :: N₁', N₂, ?_, ?_⟩
        · rw [hN]; rfl
        · intro c' hc'
          rcases List.mem_cons.mp hc' with h1 | h2
          · rw [h1]; exact hc
          · exact h_all c' h2

/-! ### Encoding positional helpers

For `decides_pos` (some empty clause exists) and `decides_neg`
(no empty clause), we need positional facts about `encodeInput`. We
factor out the dependent-`Fin` complications via `generalize` + `subst`
on an explicit list equation. -/

/-- `encodeCnf (N₁ ++ [] :: N₂)` splits at the empty clause's `4` marker. -/
private theorem encodeCnf_split_with_empty (N₁ N₂ : cnf) :
    encodeCnf (N₁ ++ ([] : clause) :: N₂) =
      ((N₁.map encodeClause).flatten ++ [4]) ++
        ((N₂.map encodeClause).flatten ++ [5]) := by
  show ((N₁ ++ ([] : clause) :: N₂).map encodeClause).flatten ++ [5] = _
  rw [List.map_append, List.map_cons, List.flatten_append]
  show ((N₁.map encodeClause).flatten ++
        ([4] ++ (N₂.map encodeClause).flatten)) ++ [5] = _
  rw [← List.append_assoc (N₁.map encodeClause).flatten [4]
        (N₂.map encodeClause).flatten]
  rw [List.append_assoc ((N₁.map encodeClause).flatten ++ [4])
        (N₂.map encodeClause).flatten [5]]

/-- For positions inside the `N₁` prefix, `encodeInput (N₁ ++ [] :: N₂, a)`
matches `(N₁.map encodeClause).flatten`. -/
private theorem encodeInput_get_in_N1_prefix (N₁ N₂ : cnf) (a : assgn)
    (k : Nat) (h_k : k < (N₁.map encodeClause).flatten.length) :
    ∃ (h : k < (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).length),
      (encodeInput (N₁ ++ ([] : clause) :: N₂, a))[k]'h =
        ((N₁.map encodeClause).flatten)[k]'h_k := by
  have h_eq_cnf := encodeCnf_split_with_empty N₁ N₂
  show ∃ (h : k <
        (encodeCnf (N₁ ++ ([] : clause) :: N₂) ++ encodeAssgn a).length),
      (encodeCnf (N₁ ++ ([] : clause) :: N₂) ++ encodeAssgn a)[k]'h =
        ((N₁.map encodeClause).flatten)[k]'h_k
  generalize h_gen : encodeCnf (N₁ ++ ([] : clause) :: N₂) = enc at h_eq_cnf ⊢
  subst h_eq_cnf
  -- Goal: ∃ h, (((N₁.flat ++ [4]) ++ (N₂.flat ++ [5])) ++ encodeAssgn a)[k]'h
  --              = (N₁.flat)[k]'h_k
  have h_lt_N1_plus : k < ((N₁.map encodeClause).flatten ++ [4]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have h_lt_inner :
      k < (((N₁.map encodeClause).flatten ++ [4]) ++
            ((N₂.map encodeClause).flatten ++ [5])).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_N1_plus
      (Nat.le_add_right _ _)
  have h_lt_full :
      k < ((((N₁.map encodeClause).flatten ++ [4]) ++
            ((N₂.map encodeClause).flatten ++ [5])) ++ encodeAssgn a).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_inner
      (Nat.le_add_right _ _)
  refine ⟨h_lt_full, ?_⟩
  rw [List.getElem_append_left h_lt_inner]
  rw [List.getElem_append_left h_lt_N1_plus]
  exact List.getElem_append_left h_k

/-- Position `(N₁.map encodeClause).flatten.length` of
`encodeInput (N₁ ++ [] :: N₂, a)` is the `4` marker of the empty clause. -/
private theorem encodeInput_get_at_empty_marker (N₁ N₂ : cnf) (a : assgn) :
    ∃ (h : (N₁.map encodeClause).flatten.length <
            (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).length),
      (encodeInput (N₁ ++ ([] : clause) :: N₂, a))[
          (N₁.map encodeClause).flatten.length]'h = 4 := by
  have h_eq_cnf := encodeCnf_split_with_empty N₁ N₂
  show ∃ (h : (N₁.map encodeClause).flatten.length <
        (encodeCnf (N₁ ++ ([] : clause) :: N₂) ++ encodeAssgn a).length),
      (encodeCnf (N₁ ++ ([] : clause) :: N₂) ++ encodeAssgn a)[
          (N₁.map encodeClause).flatten.length]'h = 4
  generalize h_gen : encodeCnf (N₁ ++ ([] : clause) :: N₂) = enc at h_eq_cnf ⊢
  subst h_eq_cnf
  have h_lt_N1_plus : (N₁.map encodeClause).flatten.length <
      ((N₁.map encodeClause).flatten ++ [4]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have h_lt_inner : (N₁.map encodeClause).flatten.length <
      (((N₁.map encodeClause).flatten ++ [4]) ++
        ((N₂.map encodeClause).flatten ++ [5])).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_N1_plus
      (Nat.le_add_right _ _)
  have h_lt_full : (N₁.map encodeClause).flatten.length <
      ((((N₁.map encodeClause).flatten ++ [4]) ++
        ((N₂.map encodeClause).flatten ++ [5])) ++ encodeAssgn a).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_inner
      (Nat.le_add_right _ _)
  refine ⟨h_lt_full, ?_⟩
  rw [List.getElem_append_left h_lt_inner]
  rw [List.getElem_append_left h_lt_N1_plus]
  exact List.getElem_concat_length rfl h_lt_N1_plus

/-- For positions inside the full CNF flatten of `N`, `encodeInput (N, a)`
matches `(N.map encodeClause).flatten`. Used in `decides_neg`. -/
private theorem encodeInput_get_in_cnf_prefix (N : cnf) (a : assgn)
    (k : Nat) (h_k : k < (N.map encodeClause).flatten.length) :
    ∃ (h : k < (encodeInput (N, a)).length),
      (encodeInput (N, a))[k]'h = ((N.map encodeClause).flatten)[k]'h_k := by
  show ∃ (h : k < ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a).length),
      ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a)[k]'h =
        ((N.map encodeClause).flatten)[k]'h_k
  have h_lt_N : k < ((N.map encodeClause).flatten ++ [5]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have h_lt_full :
      k < ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_N
      (Nat.le_add_right _ _)
  refine ⟨h_lt_full, ?_⟩
  rw [List.getElem_append_left h_lt_N]
  exact List.getElem_append_left h_k

/-- Position `(N.map encodeClause).flatten.length` of `encodeInput (N, a)`
is the `5` CNF/assgn boundary marker. Used in `decides_neg`. -/
private theorem encodeInput_get_at_cnf_5_marker (N : cnf) (a : assgn) :
    ∃ (h : (N.map encodeClause).flatten.length < (encodeInput (N, a)).length),
      (encodeInput (N, a))[(N.map encodeClause).flatten.length]'h = 5 := by
  show ∃ (h : (N.map encodeClause).flatten.length <
        ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a).length),
      ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a)[
          (N.map encodeClause).flatten.length]'h = 5
  have h_lt_N : (N.map encodeClause).flatten.length <
      ((N.map encodeClause).flatten ++ [5]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have h_lt_full : (N.map encodeClause).flatten.length <
      ((N.map encodeClause).flatten ++ [5] ++ encodeAssgn a).length := by
    rw [List.length_append]; exact Nat.lt_of_lt_of_le h_lt_N
      (Nat.le_add_right _ _)
  refine ⟨h_lt_full, ?_⟩
  rw [List.getElem_append_left h_lt_N]
  exact List.getElem_concat_length rfl h_lt_N

/-! ### `encodeCnf` length is bounded by encoded-input size. -/

private theorem encodeCnf_flat_length_le (N : cnf) (a : assgn) :
    (N.map encodeClause).flatten.length ≤ encodable.size (N, a) + 1 := by
  have h_le1 : (N.map encodeClause).flatten.length ≤ (encodeCnf N).length := by
    show (N.map encodeClause).flatten.length ≤
      ((N.map encodeClause).flatten ++ [5]).length
    rw [List.length_append]; exact Nat.le_add_right _ _
  have h_le2 : (encodeCnf N).length ≤ (encodeInput (N, a)).length := by
    show (encodeCnf N).length ≤ (encodeCnf N ++ encodeAssgn a).length
    rw [List.length_append]; exact Nat.le_add_right _ _
  exact Nat.le_trans (Nat.le_trans h_le1 h_le2) (encodeInput_length_le N a)

/-! ### Time-bound auxiliaries. -/

theorem timeBound_inOPoly : inOPoly (fun n : Nat => n + 2) :=
  inOPoly_add inOPoly_id (inOPoly_const 2)

theorem timeBound_monotonic : monotonic (fun n : Nat => n + 2) := by
  intro a b h
  exact Nat.add_le_add_right h 2

/-! ### Reformulation of the predicate for decidability.

`∃ c ∈ N, c = []` is decidable; for ergonomic `Decidable` inference
we phrase the predicate as `Na.1.any (·.isEmpty)`. We package this
phrasing in the `DecidesBy` witness and let `inTimePolyTM_iff` repackage
it back to `∃ c ∈ N, c = []` at no TM cost. -/

private def hasEmptyClause (N : cnf) : Prop := ∃ c ∈ N, c = []

private instance hasEmptyClauseDecidable (N : cnf) : Decidable (hasEmptyClause N) :=
  inferInstanceAs (Decidable (∃ c ∈ N, c = []))

/-! ### The decider witness. -/

/-- The TM-backed decider for "the CNF contains an empty clause". -/
noncomputable def decider : DecidesBy
    (fun Na : cnf × assgn => ∃ c ∈ Na.1, c = [])
    (fun n => n + 2) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 2
  rejectState := 3
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ h_ex
    rcases first_empty_clause_split N h_ex with ⟨N₁, N₂, hN_eq, h_N₁_ne⟩
    subst hN_eq
    -- Walk past N₁, then accept on the `4`.
    set L₁ := (N₁.map encodeClause).flatten.length with hL₁
    -- Build h_match for the walker on N₁.
    have h_match : ∀ k (h_k : k < (N₁.map encodeClause).flatten.length),
        ∃ (h : 0 + k <
            (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).length),
          (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).get ⟨0 + k, h⟩ =
            ((N₁.map encodeClause).flatten).get ⟨k, h_k⟩ := by
      intro k h_k
      rcases encodeInput_get_in_N1_prefix N₁ N₂ a k h_k with ⟨h_lt, h_get⟩
      have h_zero_eq : (0 : Nat) + k = k := Nat.zero_add k
      have h_lt' : 0 + k <
          (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).length :=
        h_zero_eq.symm ▸ h_lt
      refine ⟨h_lt', ?_⟩
      have heq : (⟨0 + k, h_lt'⟩ :
            Fin (encodeInput (N₁ ++ ([] : clause) :: N₂, a)).length) =
          ⟨k, h_lt⟩ := Fin.eq_of_val_eq h_zero_eq
      rw [heq]
      exact h_get
    have h_walk := TM_run_walk_clauses N₁ h_N₁_ne []
      (encodeInput (N₁ ++ ([] : clause) :: N₂, a)) 0 h_match
    -- h_walk : runFlatTM L₁ TM cfg_0 = some { state := 0, head := 0 + L₁, tape := encodeInput }
    have h_zero_add : (0 : Nat) + (N₁.map encodeClause).flatten.length =
        (N₁.map encodeClause).flatten.length := Nat.zero_add _
    rw [h_zero_add] at h_walk
    -- Read the `4` marker.
    rcases encodeInput_get_at_empty_marker N₁ N₂ a with ⟨h_L₁_lt, h_get_4⟩
    have h_step_accept :=
      TM_step_s0_accept_4 [] (encodeInput (N₁ ++ ([] : clause) :: N₂, a))
        (N₁.map encodeClause).flatten.length h_L₁_lt h_get_4
    have h_mid_not_halt :
        haltingStateReached TM
          { state_idx := 0,
            tapes := [([], (N₁.map encodeClause).flatten.length,
                       encodeInput (N₁ ++ ([] : clause) :: N₂, a))] } = false := rfl
    have h_chain := AssgnEmpty.runFlatTM_extend_by_step TM
      (N₁.map encodeClause).flatten.length _ _ _
      h_walk h_mid_not_halt h_step_accept
    have h_final_halt :
        haltingStateReached TM
          { state_idx := 2,
            tapes := [([], (N₁.map encodeClause).flatten.length,
                       encodeInput (N₁ ++ ([] : clause) :: N₂, a))] } = true := rfl
    -- Pad to budget: `encodable.size + 2`.
    have h_le : (N₁.map encodeClause).flatten.length + 1 ≤
        encodable.size (N₁ ++ ([] : clause) :: N₂, a) + 2 := by
      have h_le_size := encodeCnf_flat_length_le (N₁ ++ ([] : clause) :: N₂) a
      have h_N1_le : (N₁.map encodeClause).flatten.length ≤
          ((N₁ ++ ([] : clause) :: N₂).map encodeClause).flatten.length := by
        rw [List.map_append, List.flatten_append, List.length_append]
        exact Nat.le_add_right _ _
      omega
    rcases Nat.le.dest h_le with ⟨k, h_k⟩
    have h_padded :=
      TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
    rw [h_k] at h_padded
    refine ⟨_, ?_, h_final_halt, rfl⟩
    show runFlatTM (encodable.size (N₁ ++ ([] : clause) :: N₂, a) + 2) TM
        (initFlatConfig TM
          (initialTapes TM (encodeInput (N₁ ++ ([] : clause) :: N₂, a)))) = _
    show runFlatTM (encodable.size (N₁ ++ ([] : clause) :: N₂, a) + 2) TM
        { state_idx := 0,
          tapes := [([], 0, encodeInput (N₁ ++ ([] : clause) :: N₂, a))] } = _
    exact h_padded
  decides_neg := by
    rintro ⟨N, a⟩ h_no_empty
    -- All clauses in N are non-empty.
    have h_N_ne : ∀ c ∈ N, c ≠ [] := fun c hc h_eq => h_no_empty ⟨c, hc, h_eq⟩
    -- Walk past all of N, then reject on the `5`.
    have h_match : ∀ k (h_k : k < (N.map encodeClause).flatten.length),
        ∃ (h : 0 + k < (encodeInput (N, a)).length),
          (encodeInput (N, a)).get ⟨0 + k, h⟩ =
            ((N.map encodeClause).flatten).get ⟨k, h_k⟩ := by
      intro k h_k
      rcases encodeInput_get_in_cnf_prefix N a k h_k with ⟨h_lt, h_get⟩
      have h_zero_eq : (0 : Nat) + k = k := Nat.zero_add k
      have h_lt' : 0 + k < (encodeInput (N, a)).length := h_zero_eq.symm ▸ h_lt
      refine ⟨h_lt', ?_⟩
      have heq : (⟨0 + k, h_lt'⟩ : Fin (encodeInput (N, a)).length) =
          ⟨k, h_lt⟩ := Fin.eq_of_val_eq h_zero_eq
      rw [heq]
      exact h_get
    have h_walk := TM_run_walk_clauses N h_N_ne []
      (encodeInput (N, a)) 0 h_match
    have h_zero_add :
        (0 : Nat) + (N.map encodeClause).flatten.length =
          (N.map encodeClause).flatten.length := Nat.zero_add _
    rw [h_zero_add] at h_walk
    -- Read the `5` marker.
    rcases encodeInput_get_at_cnf_5_marker N a with ⟨h_L_lt, h_get_5⟩
    have h_step_reject :=
      TM_step_s0_reject_5 [] (encodeInput (N, a))
        (N.map encodeClause).flatten.length h_L_lt h_get_5
    have h_mid_not_halt :
        haltingStateReached TM
          { state_idx := 0,
            tapes := [([], (N.map encodeClause).flatten.length,
                       encodeInput (N, a))] } = false := rfl
    have h_chain := AssgnEmpty.runFlatTM_extend_by_step TM
      (N.map encodeClause).flatten.length _ _ _
      h_walk h_mid_not_halt h_step_reject
    have h_final_halt :
        haltingStateReached TM
          { state_idx := 3,
            tapes := [([], (N.map encodeClause).flatten.length,
                       encodeInput (N, a))] } = true := rfl
    have h_le : (N.map encodeClause).flatten.length + 1 ≤
        encodable.size (N, a) + 2 := by
      have h_le_size := encodeCnf_flat_length_le N a
      omega
    rcases Nat.le.dest h_le with ⟨k, h_k⟩
    have h_padded :=
      TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
    rw [h_k] at h_padded
    refine ⟨_, ?_, h_final_halt, rfl⟩
    show runFlatTM (encodable.size (N, a) + 2) TM
        (initFlatConfig TM (initialTapes TM (encodeInput (N, a)))) = _
    show runFlatTM (encodable.size (N, a) + 2) TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, a))] } = _
    exact h_padded

/-- "The CNF contains an empty clause" is in TM-backed polynomial time. -/
theorem inTimePolyTM_cnfHasEmptyClause :
    inTimePolyTM (fun Na : cnf × assgn => ∃ c ∈ Na.1, c = []) :=
  ⟨fun n => n + 2, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end CnfHasEmptyClause

/-! ## `AssgnContainsZero`: a 5-state walker (alternating in the assignment)

The predicate is `0 ∈ Na.2` — the assignment contains a `0` entry. In
the encoding, a "zero variable" is an EMPTY unary segment between two
separators (`5 6 …` or `6 6 …`).

States:
- 0: scanning CNF, looking for `5`.
- 1: just past `5` or `6` — expecting next variable's unary digits.
- 2: in middle of variable (saw `1`s after the last separator).
- 3: ACCEPT (saw `6` in state 1 — current variable is 0).
- 4: REJECT.

This mirrors `CnfHasEmptyClause`'s alternating-state pattern but inside
the assignment. Time bound: `n + 2`. -/

namespace AssgnContainsZero

def TM : FlatTM where
  sig := sigSAT
  tapes := 1
  states := 5
  trans :=
    let s0_advance_5 : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_none : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [none], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_accept_6 : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 6], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_enter_1 : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s1_reject_0 : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some 0], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_reject_none : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [none], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s2_continue_1 : FlatTMTransEntry :=
      { src_state := 2, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s2_separator_6 : FlatTMTransEntry :=
      { src_state := 2, src_tape_vals := [some 6], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s2_reject_0 : FlatTMTransEntry :=
      { src_state := 2, src_tape_vals := [some 0], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s2_reject_none : FlatTMTransEntry :=
      { src_state := 2, src_tape_vals := [none], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_continue (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 0,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some v], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s1_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 1, src_tape_vals := [some v], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s2_reject_symbol (v : Nat) : FlatTMTransEntry :=
      { src_state := 2, src_tape_vals := [some v], dst_state := 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    s0_advance_5 :: s0_reject_none ::
    s1_accept_6 :: s1_enter_1 :: s1_reject_0 :: s1_reject_none ::
    s2_continue_1 :: s2_separator_6 :: s2_reject_0 :: s2_reject_none ::
      (((List.range sigSAT).filter
            (fun v => decide (v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4))).map s0_continue ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 6))).map s0_reject_symbol ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5))).map s1_reject_symbol ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5))).map s2_reject_symbol)
  start := 0
  halt := [false, false, false, true, true]

private def s0_advance_5_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_none_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [none], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_accept_6_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 6], dst_state := 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_enter_1_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s1_reject_0_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some 0], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_reject_none_entry : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [none], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s2_continue_1_entry : FlatTMTransEntry :=
  { src_state := 2, src_tape_vals := [some 1], dst_state := 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s2_separator_6_entry : FlatTMTransEntry :=
  { src_state := 2, src_tape_vals := [some 6], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s2_reject_0_entry : FlatTMTransEntry :=
  { src_state := 2, src_tape_vals := [some 0], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s2_reject_none_entry : FlatTMTransEntry :=
  { src_state := 2, src_tape_vals := [none], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_continue_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 0,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s1_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 1, src_tape_vals := [some v], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s2_reject_symbol_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 2, src_tape_vals := [some v], dst_state := 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq :
    TM.trans =
      s0_advance_5_entry :: s0_reject_none_entry ::
      s1_accept_6_entry :: s1_enter_1_entry ::
      s1_reject_0_entry :: s1_reject_none_entry ::
      s2_continue_1_entry :: s2_separator_6_entry ::
      s2_reject_0_entry :: s2_reject_none_entry ::
      (((List.range sigSAT).filter
            (fun v => decide (v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4))).map s0_continue_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 0 ∨ v = 6))).map s0_reject_symbol_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5))).map s1_reject_symbol_entry ++
        ((List.range sigSAT).filter
            (fun v => decide (v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5))).map s2_reject_symbol_entry) := rfl

theorem TM_valid : validFlatTM TM := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 5; decide
  · show [false, false, false, true, true].length = 5; rfl
  · intro entry hentry
    show flatTMTransEntryValid TM entry
    rw [TM_trans_eq] at hentry
    -- Walk the 10 explicit entries, then the 4 filter blocks.
    rcases List.mem_cons.mp hentry with h | h1
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 5; decide
      · show 1 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 5 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h1 with h | h2
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h2 with h | h3
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 1 < 5; decide
      · show 3 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 6] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 6 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h3 with h | h4
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 1 < 5; decide
      · show 2 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 1] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 1 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h4 with h | h5
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 1 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 0] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 0 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h5 with h | h6
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 1 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h6 with h | h7
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 2 < 5; decide
      · show 2 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 1] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 1 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h7 with h | h8
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 2 < 5; decide
      · show 1 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 6] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 6 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h8 with h | h9
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 2 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([some 0] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 0 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h9 with h | hAppend
    · subst h
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 2 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    -- Four filter blocks: (s0_cont ++ s0_rej) ++ s1_rej ++ s2_rej.
    rcases List.mem_append.mp hAppend with hL | hS2Rej
    · rcases List.mem_append.mp hL with hL2 | hS1Rej
      · rcases List.mem_append.mp hL2 with hS0Cont | hS0Rej
        · rcases List.mem_map.mp hS0Cont with ⟨v, hv, hmk⟩
          subst hmk
          have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 0 < 5; decide
          · show 0 < 5; decide
          · intro x hx; have hx' : x ∈ ([some v] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
          · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; trivial
        · rcases List.mem_map.mp hS0Rej with ⟨v, hv, hmk⟩
          subst hmk
          have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 0 < 5; decide
          · show 4 < 5; decide
          · intro x hx; have hx' : x ∈ ([some v] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
          · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
            rw [List.mem_singleton] at hx'; subst hx'; trivial
      · rcases List.mem_map.mp hS1Rej with ⟨v, hv, hmk⟩
        subst hmk
        have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 1 < 5; decide
        · show 4 < 5; decide
        · intro x hx; have hx' : x ∈ ([some v] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
        · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
          rw [List.mem_singleton] at hx'; subst hx'; trivial
    · rcases List.mem_map.mp hS2Rej with ⟨v, hv, hmk⟩
      subst hmk
      have hvlt : v < sigSAT := List.mem_range.mp (List.mem_filter.mp hv).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 2 < 5; decide
      · show 4 < 5; decide
      · intro x hx; have hx' : x ∈ ([some v] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; exact hvlt
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial

/-! ### `applyTransitionEntry` helpers (Nmove / Rmove on a single tape). -/

private theorem applyEntry_Nmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

private theorem applyEntry_Rmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Rmove] } =
      some { state_idx := new_state, tapes := [(left, head + 1, right)] } := rfl

/-! ### Step lemmas

For each (state, symbol-class) pair the TM enters during a successful
run, we prove `stepFlatTM TM { … }` reduces to the right successor
configuration. The pattern mirrors `AssgnEmpty`'s step lemmas. -/

/-- State 0, sym = `some 5`: advance to state 1, head + 1. -/
theorem TM_step_s0_advance_5
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_advance_5_entry = _
  exact applyEntry_Rmove 0 1 left right head (some 5)

/-- Helper: in the `s0_continue` filtered block, find the entry for `v`
when `v ∈ {1,2,3,4}`. -/
private theorem find_s0_continue_match
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4) :
    (((List.range sigSAT).filter
          (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4))).map s0_continue_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_continue_entry v) := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have h_v_lt : v < sigSAT := by rcases h_v_in with h | h | h | h <;> (rw [h]; decide)
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_v_in
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_continue_entry w :: ws.map s0_continue_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- State 0, sym ∈ `some {1,2,3,4}`: stay in state 0, head + 1. -/
theorem TM_step_s0_continue
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4) :
    stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have h_ne5 : v ≠ 5 := by rcases h_v_in with h | h | h | h <;> (rw [h]; decide)
  -- Negative match for state-0 entry with sym = some 5.
  have hNot_advance5 : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne5 h2.symm
    simp [h_ne]
  -- Negative match for state-0 entry with sym = none (we're inside right).
  have hNot_state0_none : entryMatchesConfig s0_reject_none_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, hNot_advance5]
  rw [List.find?_cons, hNot_state0_none]
  -- Eight state-mismatched entries (states 1 and 2): all reduce by `rfl`
  -- since `(s == 0)` is `false` for s ∈ {1,2}, and `false && _ = false`.
  rw [List.find?_cons,
      show entryMatchesConfig s1_accept_6_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_enter_1_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_0_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_none_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s2_continue_1_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s2_separator_6_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s2_reject_0_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s2_reject_none_entry
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl]
  -- Now we hit the appended filter blocks. Find in s0_continue block.
  rw [List.find?_append, List.find?_append, List.find?_append]
  rw [find_s0_continue_match left right head v h_head_lt h_get h_v_in]
  show applyTransitionEntry _ (s0_continue_entry v) = _
  exact applyEntry_Rmove 0 0 left right head (some v)

/-- State 1, sym = `some 6`: accept (state 3). Found a zero-length variable
between separators, which means `0 ∈ a`. -/
theorem TM_step_s1_accept_6
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 6
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s1_accept_6_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 6] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons,
      show entryMatchesConfig s0_advance_5_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s0_reject_none_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_accept_6_entry = _
  exact applyEntry_Nmove 1 3 left right head (some 6)

/-- State 1, sym = `some 1`: enter variable, go to state 2, head + 1. -/
theorem TM_step_s1_enter_1
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 1
    rw [dif_pos h_head_lt, h_get]
  have hNot_acc6 : entryMatchesConfig s1_accept_6_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 6] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 6] : List (Option Nat)) ≠ [some 1] := by
      intro h; injection h with h1; injection h1 with h2; exact absurd h2 (by decide)
    simp [h_ne]
  have hMatch : entryMatchesConfig s1_enter_1_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons,
      show entryMatchesConfig s0_advance_5_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s0_reject_none_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons, hNot_acc6]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_enter_1_entry = _
  exact applyEntry_Rmove 1 2 left right head (some 1)

/-- State 1, sym = `some 0`: reject (state 4). No zero variable found,
hit the assignment terminator. -/
theorem TM_step_s1_reject_0
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 4, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 0
    rw [dif_pos h_head_lt, h_get]
  have hNot_acc6 : entryMatchesConfig s1_accept_6_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 6] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 6] : List (Option Nat)) ≠ [some 0] := by
      intro h; injection h with h1; injection h1 with h2; exact absurd h2 (by decide)
    simp [h_ne]
  have hNot_ent1 : entryMatchesConfig s1_enter_1_entry
      { state_idx := 1, tapes := [(left, head, right)] } = false := by
    show ((1 : Nat) == 1 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 1] : List (Option Nat)) ≠ [some 0] := by
      intro h; injection h with h1; injection h1 with h2; exact absurd h2 (by decide)
    simp [h_ne]
  have hMatch : entryMatchesConfig s1_reject_0_entry
      { state_idx := 1, tapes := [(left, head, right)] } = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons,
      show entryMatchesConfig s0_advance_5_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s0_reject_none_entry
        { state_idx := 1, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons, hNot_acc6]
  rw [List.find?_cons, hNot_ent1]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ s1_reject_0_entry = _
  exact applyEntry_Nmove 1 4 left right head (some 0)

/-- State 2, sym = `some 1`: continue reading the variable, head + 1. -/
theorem TM_step_s2_continue_1
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM TM { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 1
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s2_continue_1_entry
      { state_idx := 2, tapes := [(left, head, right)] } = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 2, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons,
      show entryMatchesConfig s0_advance_5_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s0_reject_none_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_accept_6_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_enter_1_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_0_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_none_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ s2_continue_1_entry = _
  exact applyEntry_Rmove 2 2 left right head (some 1)

/-- State 2, sym = `some 6`: end of nonzero variable, go to state 1, head + 1. -/
theorem TM_step_s2_separator_6
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM TM { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 6
    rw [dif_pos h_head_lt, h_get]
  have hNot_cont1 : entryMatchesConfig s2_continue_1_entry
      { state_idx := 2, tapes := [(left, head, right)] } = false := by
    show ((2 : Nat) == 2 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 1] : List (Option Nat)) ≠ [some 6] := by
      intro h; injection h with h1; injection h1 with h2; exact absurd h2 (by decide)
    simp [h_ne]
  have hMatch : entryMatchesConfig s2_separator_6_entry
      { state_idx := 2, tapes := [(left, head, right)] } = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 6] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind (TM.trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 2, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons,
      show entryMatchesConfig s0_advance_5_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s0_reject_none_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_accept_6_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_enter_1_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_0_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons,
      show entryMatchesConfig s1_reject_none_entry
        { state_idx := 2, tapes := [(left, head, right)] } = false from rfl]
  rw [List.find?_cons, hNot_cont1]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ s2_separator_6_entry = _
  exact applyEntry_Rmove 2 1 left right head (some 6)

/-! ### `runFlatTM` unfolding helpers for non-halting states. -/

private theorem runFlatTM_state0_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 0, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 0, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

private theorem runFlatTM_state1_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 1, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 1, tapes := [(left, head, right)] } = true then
          some { state_idx := 1, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 1, tapes := [(left, head, right)] } with
          | none => some { state_idx := 1, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 1, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

private theorem runFlatTM_state2_unfold (n : Nat) (left right : List Nat) (head : Nat)
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM TM { state_idx := 2, tapes := [(left, head, right)] } = some cfg') :
    runFlatTM (n + 1) TM { state_idx := 2, tapes := [(left, head, right)] } =
      runFlatTM n TM cfg' := by
  show (if haltingStateReached TM { state_idx := 2, tapes := [(left, head, right)] } = true then
          some { state_idx := 2, tapes := [(left, head, right)] }
        else
          match stepFlatTM TM { state_idx := 2, tapes := [(left, head, right)] } with
          | none => some { state_idx := 2, tapes := [(left, head, right)] }
          | some cfg'' => runFlatTM n TM cfg'') = _
  have h_not_halt : haltingStateReached TM
      { state_idx := 2, tapes := [(left, head, right)] } = false := rfl
  rw [h_not_halt, h_step]
  rfl

/-! ### Phase 1 run lemma: walk state 0 through the CNF until reaching `5`. -/

/-- Starting at state 0 with head at `head`, given the tape contains a `5`
at position `head + gap` and symbols in `{1,2,3,4}` at positions
`head..head+gap-1`, after `gap + 1` steps we are in state 1 at
`head + gap + 1`. -/
private theorem TM_run_scan_to_5
    (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = 5 →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ = 1 ∨
        right.get ⟨head + k, h⟩ = 2 ∨
        right.get ⟨head + k, h⟩ = 3 ∨
        right.get ⟨head + k, h⟩ = 4) →
      runFlatTM (gap + 1) TM
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, head + gap + 1, right)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get_5 : right.get ⟨head, h_lt⟩ = 5 := by
        have := h_get_target
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [heq] at this; exact this
      rw [runFlatTM_state0_unfold 0 left right head _
        (TM_step_s0_advance_5 left right head h_lt h_get_5)]
      show (some { state_idx := 1, tapes := [(left, head + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + 0 + 1, right)] }
      rw [Nat.add_zero]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_v⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_get_head_v : right.get ⟨head, h_head_lt⟩ = 1 ∨
          right.get ⟨head, h_head_lt⟩ = 2 ∨
          right.get ⟨head, h_head_lt⟩ = 3 ∨
          right.get ⟨head, h_head_lt⟩ = 4 := by
        rw [heq0] at h_v; exact h_v
      have h_step := TM_step_s0_continue left right head
        (right.get ⟨head, h_head_lt⟩) h_head_lt rfl h_get_head_v
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range' : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head + 1) + gap, h_in_range'⟩ = 5 := by
        have heq : (⟨(head + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < right.length),
            right.get ⟨(head + 1) + k, h⟩ = 1 ∨
            right.get ⟨(head + 1) + k, h⟩ = 2 ∨
            right.get ⟨(head + 1) + k, h⟩ = 3 ∨
            right.get ⟨(head + 1) + k, h⟩ = 4 := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk', h_v'⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk'' : (head + 1) + k < right.length := hShift ▸ h_kk'
        refine ⟨h_kk'', ?_⟩
        have heq : (⟨(head + 1) + k, h_kk''⟩ : Fin right.length) =
            ⟨head + (k + 1), h_kk'⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h_v'
      have hih :=
        TM_run_scan_to_5 left right gap (head + 1) h_in_range' h_get_target' h_before'
      rw [runFlatTM_state0_unfold (gap + 1) left right head _ h_step]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (head + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + (gap + 1) + 1, right)] }
      rw [h_succ]
  termination_by gap _ _ _ _ => gap

/-! ### Phase 2 run lemmas: walking the assignment from state 1. -/

/-- From state 2, walking through `k` ones followed by a `6`, in `k + 1`
steps we are in state 1 at position `p + k + 1`. -/
private theorem TM_run_walk_state2_to_state1
    (left right : List Nat) :
    ∀ (k p : Nat),
      (∀ i, i < k → ∃ (h : p + i < right.length),
        right.get ⟨p + i, h⟩ = 1) →
      (∃ (h : p + k < right.length),
        right.get ⟨p + k, h⟩ = 6) →
      runFlatTM (k + 1) TM { state_idx := 2, tapes := [(left, p, right)] } =
        some { state_idx := 1, tapes := [(left, p + k + 1, right)] }
  | 0, p, _, h_six => by
      rcases h_six with ⟨h_lt, h_get⟩
      have h_lt0' : p < right.length := by
        have := h_lt; rwa [Nat.add_zero] at this
      have h_get0 : right.get ⟨p, h_lt0'⟩ = 6 := by
        have heq : (⟨p + 0, h_lt⟩ : Fin right.length) = ⟨p, h_lt0'⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_get; exact h_get
      rw [runFlatTM_state2_unfold 0 left right p _
        (TM_step_s2_separator_6 left right p h_lt0' h_get0)]
      show (some { state_idx := 1, tapes := [(left, p + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, p + 0 + 1, right)] }
      rw [Nat.add_zero]
  | k + 1, p, h_ones, h_six => by
      rcases h_ones 0 (Nat.zero_lt_succ _) with ⟨h_lt0, h_get0⟩
      have h_lt0' : p < right.length := by
        have := h_lt0; rwa [Nat.add_zero] at this
      have h_get0' : right.get ⟨p, h_lt0'⟩ = 1 := by
        have heq : (⟨p + 0, h_lt0⟩ : Fin right.length) = ⟨p, h_lt0'⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_get0; exact h_get0
      have h_step := TM_step_s2_continue_1 left right p h_lt0' h_get0'
      have h_ones' : ∀ i, i < k → ∃ (h : (p + 1) + i < right.length),
          right.get ⟨(p + 1) + i, h⟩ = 1 := by
        intro i hi
        rcases h_ones (i + 1) (Nat.succ_lt_succ hi) with ⟨h_lt, h_get⟩
        have hShift : p + (i + 1) = (p + 1) + i := by
          rw [Nat.add_assoc, Nat.add_comm 1 i]
        have h_lt' : (p + 1) + i < right.length := hShift ▸ h_lt
        refine ⟨h_lt', ?_⟩
        have heq : (⟨(p + 1) + i, h_lt'⟩ : Fin right.length) =
            ⟨p + (i + 1), h_lt⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h_get
      have h_six' : ∃ (h : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h⟩ = 6 := by
        rcases h_six with ⟨h_lt, h_get⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_lt' : (p + 1) + k < right.length := hShift ▸ h_lt
        refine ⟨h_lt', ?_⟩
        have heq : (⟨(p + 1) + k, h_lt'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_lt⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h_get
      have hih := TM_run_walk_state2_to_state1 left right k (p + 1) h_ones' h_six'
      rw [runFlatTM_state2_unfold (k + 1) left right p _ h_step]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (p + 1) + k + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, p + (k + 1) + 1, right)] }
      have hShift : (p + 1) + k + 1 = p + (k + 1) + 1 := by
        rw [Nat.add_assoc p 1 k, Nat.add_comm 1 k]
      rw [hShift]
  termination_by k _ _ _ => k

/-- From state 1 with head at `p`, walking one nonzero variable (encoded as
`v` ones followed by a `6`), in `v + 1` steps we are in state 1 at
position `p + v + 1`. -/
private theorem TM_run_walk_one_nonzero_var
    (left right : List Nat) (p v : Nat) (h_v_pos : 0 < v)
    (h_ones : ∀ i, i < v → ∃ (h : p + i < right.length),
      right.get ⟨p + i, h⟩ = 1)
    (h_six : ∃ (h : p + v < right.length),
      right.get ⟨p + v, h⟩ = 6) :
    runFlatTM (v + 1) TM { state_idx := 1, tapes := [(left, p, right)] } =
      some { state_idx := 1, tapes := [(left, p + v + 1, right)] } := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h_v_pos) with ⟨w, hw⟩
  subst hw
  -- Step 1: state 1, p, read 1 → state 2, p+1.
  rcases h_ones 0 (Nat.zero_lt_succ _) with ⟨h_lt0, h_get0⟩
  have h_lt0' : p < right.length := by
    have := h_lt0; rwa [Nat.add_zero] at this
  have h_get0' : right.get ⟨p, h_lt0'⟩ = 1 := by
    have heq : (⟨p + 0, h_lt0⟩ : Fin right.length) = ⟨p, h_lt0'⟩ :=
      Fin.eq_of_val_eq (Nat.add_zero p)
    rw [heq] at h_get0; exact h_get0
  have h_step1 := TM_step_s1_enter_1 left right p h_lt0' h_get0'
  -- Phase 2: walk w ones + 6 from state 2 at p+1.
  have h_ones' : ∀ i, i < w → ∃ (h : (p + 1) + i < right.length),
      right.get ⟨(p + 1) + i, h⟩ = 1 := by
    intro i hi
    rcases h_ones (i + 1) (Nat.succ_lt_succ hi) with ⟨h_lt, h_get⟩
    have hShift : p + (i + 1) = (p + 1) + i := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    have h_lt' : (p + 1) + i < right.length := hShift ▸ h_lt
    refine ⟨h_lt', ?_⟩
    have heq : (⟨(p + 1) + i, h_lt'⟩ : Fin right.length) =
        ⟨p + (i + 1), h_lt⟩ := Fin.eq_of_val_eq hShift.symm
    rw [heq]; exact h_get
  have h_six' : ∃ (h : (p + 1) + w < right.length),
      right.get ⟨(p + 1) + w, h⟩ = 6 := by
    rcases h_six with ⟨h_lt, h_get⟩
    have hShift : p + (w + 1) = (p + 1) + w := by
      rw [Nat.add_assoc, Nat.add_comm 1 w]
    have h_lt' : (p + 1) + w < right.length := hShift ▸ h_lt
    refine ⟨h_lt', ?_⟩
    have heq : (⟨(p + 1) + w, h_lt'⟩ : Fin right.length) =
        ⟨p + (w + 1), h_lt⟩ := Fin.eq_of_val_eq hShift.symm
    rw [heq]; exact h_get
  have h_tail := TM_run_walk_state2_to_state1 left right w (p + 1) h_ones' h_six'
  rw [runFlatTM_state1_unfold (w + 1) left right p _ h_step1]
  rw [h_tail]
  show (some { state_idx := 1, tapes := [(left, (p + 1) + w + 1, right)] }
          : Option FlatTMConfig) =
    some { state_idx := 1, tapes := [(left, p + (w + 1) + 1, right)] }
  have hShift : (p + 1) + w + 1 = p + (w + 1) + 1 := by
    rw [Nat.add_assoc p 1 w, Nat.add_comm 1 w]
  rw [hShift]

/-- The walk-length for one variable `v`: `v + 1` symbols (v ones + a 6). -/
private def oneVarChunk (v : Nat) : List Nat := List.replicate v 1 ++ [6]

private theorem oneVarChunk_length (v : Nat) : (oneVarChunk v).length = v + 1 := by
  show (List.replicate v 1 ++ [6]).length = v + 1
  rw [List.length_append, List.length_replicate, List.length_singleton]

/-- Walking through a list of nonzero variables from state 1: each variable
contributes `(replicate v 1 ++ [6])` symbols and `v + 1` steps. After
walking through all of them we are back in state 1. -/
private theorem TM_run_walk_nonzero_assgn :
    ∀ (a : assgn) (h_all : ∀ v ∈ a, 0 < v)
      (left right : List Nat) (p : Nat),
      (∀ k (h_k : k < (a.map oneVarChunk).flatten.length),
        ∃ (h : p + k < right.length),
          right.get ⟨p + k, h⟩ =
            ((a.map oneVarChunk).flatten).get ⟨k, h_k⟩) →
      runFlatTM ((a.map oneVarChunk).flatten.length) TM
          { state_idx := 1, tapes := [(left, p, right)] } =
        some { state_idx := 1,
               tapes := [(left, p + (a.map oneVarChunk).flatten.length, right)] }
  | [], _, left, right, p, _ => by
      show runFlatTM 0 TM { state_idx := 1, tapes := [(left, p, right)] } = _
      show (some { state_idx := 1, tapes := [(left, p, right)] } : Option FlatTMConfig) =
        some { state_idx := 1,
               tapes := [(left, p + (([] : assgn).map oneVarChunk).flatten.length, right)] }
      have h_zero : (([] : assgn).map oneVarChunk).flatten.length = 0 := rfl
      rw [h_zero, Nat.add_zero]
  | v :: rest, h_all, left, right, p, h_match => by
      have h_v_pos : 0 < v := h_all v (List.mem_cons.mpr (Or.inl rfl))
      have h_rest_all : ∀ w ∈ rest, 0 < w := fun w hw =>
        h_all w (List.mem_cons.mpr (Or.inr hw))
      have h_oVC_len : (oneVarChunk v).length = v + 1 := oneVarChunk_length v
      have h_len_split : ((v :: rest).map oneVarChunk).flatten.length =
          (oneVarChunk v).length + (rest.map oneVarChunk).flatten.length := by
        show (oneVarChunk v ++ (rest.map oneVarChunk).flatten).length = _
        rw [List.length_append]
      -- Tape matches positions p..p+v-1 = 1.
      have h_ones : ∀ i, i < v → ∃ (h : p + i < right.length),
          right.get ⟨p + i, h⟩ = 1 := by
        intro i hi
        have hi_oVC : i < (oneVarChunk v).length := by
          rw [h_oVC_len]; exact Nat.lt_succ_of_lt hi
        have hi_full : i < ((v :: rest).map oneVarChunk).flatten.length := by
          rw [h_len_split]
          exact Nat.lt_of_lt_of_le hi_oVC (Nat.le_add_right _ _)
        rcases h_match i hi_full with ⟨h_lt, h_get⟩
        refine ⟨h_lt, ?_⟩
        rw [h_get]
        show (oneVarChunk v ++ (rest.map oneVarChunk).flatten)[i]'hi_full = 1
        rw [List.getElem_append_left hi_oVC]
        show (List.replicate v 1 ++ [6])[i]'hi_oVC = 1
        have hi_repl : i < (List.replicate v 1).length := by
          rw [List.length_replicate]; exact hi
        rw [List.getElem_append_left hi_repl]
        have h_mem : (List.replicate v 1)[i]'hi_repl ∈ List.replicate v 1 :=
          List.getElem_mem hi_repl
        exact (List.mem_replicate.mp h_mem).2
      -- Tape matches position p+v = 6.
      have h_six : ∃ (h : p + v < right.length),
          right.get ⟨p + v, h⟩ = 6 := by
        have h_v_oVC : v < (oneVarChunk v).length := by
          rw [h_oVC_len]; exact Nat.lt_succ_self _
        have h_v_full : v < ((v :: rest).map oneVarChunk).flatten.length := by
          rw [h_len_split]
          exact Nat.lt_of_lt_of_le h_v_oVC (Nat.le_add_right _ _)
        rcases h_match v h_v_full with ⟨h_lt, h_get⟩
        refine ⟨h_lt, ?_⟩
        rw [h_get]
        show (oneVarChunk v ++ (rest.map oneVarChunk).flatten)[v]'h_v_full = 6
        rw [List.getElem_append_left h_v_oVC]
        show (List.replicate v 1 ++ [6])[v]'h_v_oVC = 6
        have h_v_repl : (List.replicate v 1).length ≤ v := by rw [List.length_replicate]
        rw [List.getElem_append_right h_v_repl]
        simp [List.length_replicate]
      have h_walk_one :=
        TM_run_walk_one_nonzero_var left right p v h_v_pos h_ones h_six
      -- Rewrite h_walk_one to use (oneVarChunk v).length for both time and position.
      have h_walk_one' :
          runFlatTM (oneVarChunk v).length TM
            { state_idx := 1, tapes := [(left, p, right)] } =
          some { state_idx := 1,
                 tapes := [(left, p + (oneVarChunk v).length, right)] } := by
        rw [h_oVC_len, ← Nat.add_assoc]
        exact h_walk_one
      -- IH: walk rest at p + (oneVarChunk v).length.
      have h_match_rest : ∀ k (h_k : k < (rest.map oneVarChunk).flatten.length),
          ∃ (h : (p + (oneVarChunk v).length) + k < right.length),
            right.get ⟨(p + (oneVarChunk v).length) + k, h⟩ =
              ((rest.map oneVarChunk).flatten).get ⟨k, h_k⟩ := by
        intro k h_k
        have h_k_full : (oneVarChunk v).length + k <
            ((v :: rest).map oneVarChunk).flatten.length := by
          rw [h_len_split]; exact Nat.add_lt_add_left h_k _
        rcases h_match ((oneVarChunk v).length + k) h_k_full with ⟨h_lt, h_get⟩
        have hShift : p + ((oneVarChunk v).length + k) =
            (p + (oneVarChunk v).length) + k := by ring
        have h_lt' : (p + (oneVarChunk v).length) + k < right.length := hShift ▸ h_lt
        refine ⟨h_lt', ?_⟩
        have heq_idx : (⟨(p + (oneVarChunk v).length) + k, h_lt'⟩ : Fin right.length) =
            ⟨p + ((oneVarChunk v).length + k), h_lt⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq_idx, h_get]
        show (oneVarChunk v ++ (rest.map oneVarChunk).flatten).get
              ⟨(oneVarChunk v).length + k, h_k_full⟩ =
            (rest.map oneVarChunk).flatten.get ⟨k, h_k⟩
        rw [List.get_eq_getElem, List.get_eq_getElem]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp
      have ih := TM_run_walk_nonzero_assgn rest h_rest_all left right
        (p + (oneVarChunk v).length) h_match_rest
      -- Compose.
      rw [h_len_split]
      have h_compose := CnfHasEmptyClause.runFlatTM_compose TM
        (oneVarChunk v).length (rest.map oneVarChunk).flatten.length _ _ h_walk_one'
      rw [h_compose, ih]
      have h_assoc : p + (oneVarChunk v).length +
          (rest.map oneVarChunk).flatten.length =
          p + ((oneVarChunk v).length + (rest.map oneVarChunk).flatten.length) :=
        Nat.add_assoc p _ _
      rw [h_assoc]
  termination_by a _ _ _ _ _ => a.length

/-! ### Encoding facts -/

/-- For an assignment `a₁ ++ 0 :: a₂` with `a₁` all-nonzero, the encoding
splits as the oneVarChunk-flatten of `a₁` followed by `6 :: encodeAssgn a₂`. -/
private theorem encodeAssgn_split_with_zero (a₁ a₂ : assgn)
    (h_all : ∀ v ∈ a₁, 0 < v) :
    encodeAssgn (a₁ ++ 0 :: a₂) =
      (a₁.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂ := by
  induction a₁ with
  | nil =>
      show encodeAssgn (0 :: a₂) = ([] : List Nat) ++ 6 :: encodeAssgn a₂
      show List.replicate 0 1 ++ 6 :: encodeAssgn a₂ = [] ++ 6 :: encodeAssgn a₂
      rfl
  | cons v rest ih =>
      have h_rest_all : ∀ w ∈ rest, 0 < w := fun w hw =>
        h_all w (List.mem_cons.mpr (Or.inr hw))
      have h_ih := ih h_rest_all
      show List.replicate v 1 ++ 6 :: encodeAssgn (rest ++ 0 :: a₂) = _
      rw [h_ih]
      show List.replicate v 1 ++ ([6] ++
          ((rest.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂)) =
          ((List.replicate v 1 ++ [6]) ++ (rest.map oneVarChunk).flatten) ++
            6 :: encodeAssgn a₂
      rw [← List.append_assoc, ← List.append_assoc]

/-- For an assignment with all-nonzero variables, the encoding equals the
oneVarChunk-flatten followed by the `[0]` terminator. -/
private theorem encodeAssgn_nonzero_eq (a : assgn) (h_all : ∀ v ∈ a, 0 < v) :
    encodeAssgn a = (a.map oneVarChunk).flatten ++ [0] := by
  induction a with
  | nil =>
      show ([0] : List Nat) = ([] : List (List Nat)).flatten ++ [0]
      rfl
  | cons v rest ih =>
      have h_rest_all : ∀ w ∈ rest, 0 < w := fun w hw =>
        h_all w (List.mem_cons.mpr (Or.inr hw))
      have h_ih := ih h_rest_all
      show List.replicate v 1 ++ 6 :: encodeAssgn rest = _
      rw [h_ih]
      show List.replicate v 1 ++ ([6] ++ ((rest.map oneVarChunk).flatten ++ [0])) =
          ((List.replicate v 1 ++ [6]) ++ (rest.map oneVarChunk).flatten) ++ [0]
      rw [← List.append_assoc, ← List.append_assoc]

/-- Split an assignment at its first zero entry: `a = a₁ ++ 0 :: a₂` with
`a₁` all-nonzero. -/
private theorem first_zero_in_assgn_split (a : assgn) (h : 0 ∈ a) :
    ∃ a₁ a₂ : assgn, a = a₁ ++ 0 :: a₂ ∧ ∀ v ∈ a₁, 0 < v := by
  induction a with
  | nil => cases h
  | cons v rest ih =>
      by_cases hv : v = 0
      · refine ⟨[], rest, ?_, ?_⟩
        · subst hv; rfl
        · intro w hw; cases hw
      · have hv_pos : 0 < v := Nat.pos_of_ne_zero hv
        have h_rest : 0 ∈ rest := by
          rcases List.mem_cons.mp h with h0 | h_in
          · exact absurd h0.symm hv
          · exact h_in
        rcases ih h_rest with ⟨a₁', a₂, hEq, h_all⟩
        refine ⟨v :: a₁', a₂, ?_, ?_⟩
        · rw [hEq]; rfl
        · intro w hw
          rcases List.mem_cons.mp hw with h1 | h2
          · rw [h1]; exact hv_pos
          · exact h_all w h2

/-! ### Scan-to-assignment-start helper

After `(encodeCnf N).length` steps the TM is in state 1 at position
`(encodeCnf N).length` (just past the `5` terminator). -/

private theorem run_scan_to_assgn_start (N : cnf) (a : assgn) :
    runFlatTM (encodeCnf N).length TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, a))] } =
      some { state_idx := 1,
             tapes := [([], (encodeCnf N).length, encodeInput (N, a))] } := by
  have h_cnf_pos := AssgnEmpty.encodeCnf_length_pos N
  have h_input_len_gt := AssgnEmpty.encodeInput_length_gt_cnf N a
  have h_5_in_cnf : (encodeCnf N).length - 1 < (encodeCnf N).length :=
    Nat.sub_lt h_cnf_pos (Nat.zero_lt_succ _)
  have h_gap_succ : (encodeCnf N).length - 1 + 1 = (encodeCnf N).length :=
    Nat.sub_add_cancel h_cnf_pos
  have h_5_in_range :
      0 + ((encodeCnf N).length - 1) < (encodeInput (N, a)).length := by
    rw [Nat.zero_add]; exact Nat.lt_trans h_5_in_cnf h_input_len_gt
  have h_5_in_input : (encodeCnf N).length - 1 < (encodeInput (N, a)).length :=
    Nat.lt_trans h_5_in_cnf h_input_len_gt
  have h_get_5 :
      (encodeInput (N, a)).get ⟨0 + ((encodeCnf N).length - 1), h_5_in_range⟩ = 5 := by
    have heq : (⟨0 + ((encodeCnf N).length - 1), h_5_in_range⟩ :
                 Fin (encodeInput (N, a)).length) =
        ⟨(encodeCnf N).length - 1, h_5_in_input⟩ :=
      Fin.eq_of_val_eq (Nat.zero_add _)
    rw [heq]
    show (encodeInput (N, a))[(encodeCnf N).length - 1]'h_5_in_input = 5
    rw [AssgnEmpty.encodeInput_get_in_cnf N a ((encodeCnf N).length - 1) h_5_in_cnf]
    exact AssgnEmpty.encodeCnf_get_last N h_5_in_cnf
  have h_before : ∀ k, k < (encodeCnf N).length - 1 →
      ∃ (h : 0 + k < (encodeInput (N, a)).length),
        (encodeInput (N, a)).get ⟨0 + k, h⟩ = 1 ∨
        (encodeInput (N, a)).get ⟨0 + k, h⟩ = 2 ∨
        (encodeInput (N, a)).get ⟨0 + k, h⟩ = 3 ∨
        (encodeInput (N, a)).get ⟨0 + k, h⟩ = 4 := by
    intro k hk
    have h_eq_cnf : encodeCnf N = (N.map encodeClause).flatten ++ [5] := rfl
    have h_k_lt_int : k < (N.map encodeClause).flatten.length := by
      have h_len_eq : (encodeCnf N).length - 1 = (N.map encodeClause).flatten.length := by
        rw [h_eq_cnf, List.length_append, List.length_singleton]; rfl
      rw [h_len_eq] at hk; exact hk
    have h_k_lt_cnf : k < (encodeCnf N).length := by
      rw [h_eq_cnf, List.length_append, List.length_singleton]
      exact Nat.lt_succ_of_lt h_k_lt_int
    have h_get_eq : (encodeCnf N)[k]'h_k_lt_cnf =
        ((N.map encodeClause).flatten)[k]'h_k_lt_int := by
      show ((N.map encodeClause).flatten ++ [5])[k]'(h_eq_cnf ▸ h_k_lt_cnf) =
        ((N.map encodeClause).flatten)[k]'h_k_lt_int
      exact List.getElem_append_left h_k_lt_int
    have h_mem : ((N.map encodeClause).flatten)[k]'h_k_lt_int ∈
        (N.map encodeClause).flatten := List.getElem_mem h_k_lt_int
    have h_in_one_to_four := AssgnEmpty.encodeCnf_interior_in_one_to_four N _ h_mem
    have h_k_input_zero : 0 + k < (encodeInput (N, a)).length := by
      rw [Nat.zero_add]; exact Nat.lt_trans h_k_lt_cnf h_input_len_gt
    have h_k_input : k < (encodeInput (N, a)).length :=
      Nat.lt_trans h_k_lt_cnf h_input_len_gt
    have heq : (⟨0 + k, h_k_input_zero⟩ : Fin (encodeInput (N, a)).length) =
        ⟨k, h_k_input⟩ := Fin.eq_of_val_eq (Nat.zero_add k)
    have h_get_input : (encodeInput (N, a)).get ⟨0 + k, h_k_input_zero⟩ =
        (encodeCnf N)[k]'h_k_lt_cnf := by
      rw [heq]
      show (encodeInput (N, a))[k]'h_k_input = (encodeCnf N)[k]'h_k_lt_cnf
      exact AssgnEmpty.encodeInput_get_in_cnf N a k h_k_lt_cnf
    refine ⟨h_k_input_zero, ?_⟩
    rw [h_get_input, h_get_eq]
    exact h_in_one_to_four
  have h_scan_run := TM_run_scan_to_5 [] (encodeInput (N, a))
    ((encodeCnf N).length - 1) 0 h_5_in_range h_get_5 h_before
  have h_idx_eq : 0 + ((encodeCnf N).length - 1) + 1 = (encodeCnf N).length := by
    rw [Nat.zero_add]; exact h_gap_succ
  rw [h_idx_eq] at h_scan_run
  rw [h_gap_succ] at h_scan_run
  exact h_scan_run

/-! ### Encoding positional helpers (for the decider) -/

/-- For an assignment `a₁ ++ 0 :: a₂` with `a₁` all-nonzero, position
`(a₁.map oneVarChunk).flatten.length` of `encodeAssgn (a₁ ++ 0 :: a₂)` is `6`. -/
private theorem encodeAssgn_get_at_walk_length (a₁ a₂ : assgn)
    (h_all : ∀ v ∈ a₁, 0 < v) :
    ∃ (h : (a₁.map oneVarChunk).flatten.length < (encodeAssgn (a₁ ++ 0 :: a₂)).length),
      (encodeAssgn (a₁ ++ 0 :: a₂))[(a₁.map oneVarChunk).flatten.length]'h = 6 := by
  have h_split := encodeAssgn_split_with_zero a₁ a₂ h_all
  generalize h_gen : encodeAssgn (a₁ ++ 0 :: a₂) = enc at h_split
  subst h_split
  have h_lt : (a₁.map oneVarChunk).flatten.length <
      ((a₁.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂).length := by
    rw [List.length_append]
    exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
  refine ⟨h_lt, ?_⟩
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp [Nat.sub_self]

/-- For an all-nonzero assignment `a`, position
`(a.map oneVarChunk).flatten.length` of `encodeAssgn a` is the `0` terminator. -/
private theorem encodeAssgn_get_at_walk_length_nonzero (a : assgn)
    (h_all : ∀ v ∈ a, 0 < v) :
    ∃ (h : (a.map oneVarChunk).flatten.length < (encodeAssgn a).length),
      (encodeAssgn a)[(a.map oneVarChunk).flatten.length]'h = 0 := by
  have h_eq := encodeAssgn_nonzero_eq a h_all
  generalize h_gen : encodeAssgn a = enc at h_eq
  subst h_eq
  have h_lt : (a.map oneVarChunk).flatten.length <
      ((a.map oneVarChunk).flatten ++ [0]).length := by
    rw [List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  refine ⟨h_lt, ?_⟩
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp [Nat.sub_self]

/-! ### Time-bound auxiliaries. -/

theorem timeBound_inOPoly : inOPoly (fun n : Nat => n + 2) :=
  inOPoly_add inOPoly_id (inOPoly_const 2)

theorem timeBound_monotonic : monotonic (fun n : Nat => n + 2) := by
  intro a b h
  exact Nat.add_le_add_right h 2

/-! ### The decider witness. -/

/-- The TM-backed decider for "the assignment contains a `0` entry". -/
noncomputable def decider : DecidesBy
    (fun Na : cnf × assgn => 0 ∈ Na.2)
    (fun n => n + 2) where
  encode := encodeInput
  encode_size := fun ⟨N, a⟩ => encodeInput_length_le N a
  M := TM
  M_valid := TM_valid
  M_tapes_pos := by decide
  acceptState := 3
  rejectState := 4
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    rintro ⟨N, a⟩ h_zero_in
    rcases first_zero_in_assgn_split a h_zero_in with ⟨a₁, a₂, h_a_eq, h_a₁_all⟩
    subst h_a_eq
    have h_enc_split : encodeAssgn (a₁ ++ 0 :: a₂) =
        (a₁.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂ :=
      encodeAssgn_split_with_zero a₁ a₂ h_a₁_all
    set L_cnf := (encodeCnf N).length with hL_cnf
    set L_walk := (a₁.map oneVarChunk).flatten.length with hL_walk
    -- Phase 1: scan CNF.
    have h_scan := run_scan_to_assgn_start N (a₁ ++ 0 :: a₂)
    -- Phase 2: walk a₁ (all nonzero) from state 1 at position L_cnf.
    have h_match : ∀ k (h_k : k < L_walk),
        ∃ (h : L_cnf + k < (encodeInput (N, a₁ ++ 0 :: a₂)).length),
          (encodeInput (N, a₁ ++ 0 :: a₂)).get ⟨L_cnf + k, h⟩ =
            ((a₁.map oneVarChunk).flatten).get ⟨k, h_k⟩ := by
      intro k h_k
      show ∃ (h : L_cnf + k < (encodeCnf N ++ encodeAssgn (a₁ ++ 0 :: a₂)).length),
          (encodeCnf N ++ encodeAssgn (a₁ ++ 0 :: a₂)).get ⟨L_cnf + k, h⟩ =
            ((a₁.map oneVarChunk).flatten).get ⟨k, h_k⟩
      rw [h_enc_split]
      have h_lt_walk : k < ((a₁.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂).length := by
        rw [List.length_append]; exact Nat.lt_of_lt_of_le h_k (Nat.le_add_right _ _)
      have h_lt_full : L_cnf + k <
          (encodeCnf N ++ ((a₁.map oneVarChunk).flatten ++ 6 :: encodeAssgn a₂)).length := by
        rw [List.length_append]; exact Nat.add_lt_add_left h_lt_walk _
      refine ⟨h_lt_full, ?_⟩
      rw [List.get_eq_getElem]
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.get_eq_getElem]
      exact List.getElem_append_left h_k
    have h_walk := TM_run_walk_nonzero_assgn a₁ h_a₁_all []
      (encodeInput (N, a₁ ++ 0 :: a₂)) L_cnf h_match
    -- Phase 3: read 6 at position L_cnf + L_walk → state 3 (accept).
    have h_6_pos : L_cnf + L_walk < (encodeInput (N, a₁ ++ 0 :: a₂)).length := by
      show L_cnf + L_walk < (encodeCnf N ++ encodeAssgn (a₁ ++ 0 :: a₂)).length
      rw [List.length_append, h_enc_split, List.length_append, List.length_cons]
      have h1 : L_walk < L_walk + ((encodeAssgn a₂).length + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos _)
      exact Nat.add_lt_add_left h1 _
    have h_get_6 : (encodeInput (N, a₁ ++ 0 :: a₂))[L_cnf + L_walk]'h_6_pos = 6 := by
      rcases encodeAssgn_get_at_walk_length a₁ a₂ h_a₁_all with ⟨_, h_get_walk⟩
      show (encodeCnf N ++ encodeAssgn (a₁ ++ 0 :: a₂))[L_cnf + L_walk]'h_6_pos = 6
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      exact h_get_walk
    have h_step_accept := TM_step_s1_accept_6 [] (encodeInput (N, a₁ ++ 0 :: a₂))
      (L_cnf + L_walk) h_6_pos h_get_6
    -- Compose: h_scan ∘ h_walk via runFlatTM_compose, then extend with h_step_accept.
    have h_scan_walk := CnfHasEmptyClause.runFlatTM_compose TM
      L_cnf L_walk _ _ h_scan
    rw [h_walk] at h_scan_walk
    have h_mid_not_halt : haltingStateReached TM
        { state_idx := 1,
          tapes := [([], L_cnf + L_walk, encodeInput (N, a₁ ++ 0 :: a₂))] } = false := rfl
    have h_chain := AssgnEmpty.runFlatTM_extend_by_step TM (L_cnf + L_walk) _ _ _
      h_scan_walk h_mid_not_halt h_step_accept
    have h_final_halt : haltingStateReached TM
        { state_idx := 3,
          tapes := [([], L_cnf + L_walk, encodeInput (N, a₁ ++ 0 :: a₂))] } = true := rfl
    -- Pad to budget encodable.size + 2.
    have h_walk_le_assgn : L_walk ≤ (encodeAssgn (a₁ ++ 0 :: a₂)).length := by
      rw [h_enc_split, List.length_append]; exact Nat.le_add_right _ _
    have h_total_len : L_cnf + (encodeAssgn (a₁ ++ 0 :: a₂)).length =
        (encodeInput (N, a₁ ++ 0 :: a₂)).length := by
      show (encodeCnf N).length + (encodeAssgn (a₁ ++ 0 :: a₂)).length =
        (encodeCnf N ++ encodeAssgn (a₁ ++ 0 :: a₂)).length
      rw [List.length_append]
    have h_input_le : (encodeInput (N, a₁ ++ 0 :: a₂)).length ≤
        encodable.size (N, a₁ ++ 0 :: a₂) + 1 :=
      encodeInput_length_le _ _
    have h_le : L_cnf + L_walk + 1 ≤ encodable.size (N, a₁ ++ 0 :: a₂) + 2 := by
      have h1 : L_cnf + L_walk ≤ L_cnf + (encodeAssgn (a₁ ++ 0 :: a₂)).length :=
        Nat.add_le_add_left h_walk_le_assgn _
      have h2 : L_cnf + L_walk ≤ (encodeInput (N, a₁ ++ 0 :: a₂)).length := by
        rw [← h_total_len]; exact h1
      have h3 : L_cnf + L_walk ≤ encodable.size (N, a₁ ++ 0 :: a₂) + 1 :=
        Nat.le_trans h2 h_input_le
      exact Nat.add_le_add_right h3 1
    rcases Nat.le.dest h_le with ⟨k, h_k⟩
    have h_padded := TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
    rw [h_k] at h_padded
    refine ⟨_, ?_, h_final_halt, rfl⟩
    show runFlatTM (encodable.size (N, a₁ ++ 0 :: a₂) + 2) TM
        (initFlatConfig TM (initialTapes TM (encodeInput (N, a₁ ++ 0 :: a₂)))) = _
    show runFlatTM (encodable.size (N, a₁ ++ 0 :: a₂) + 2) TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, a₁ ++ 0 :: a₂))] } = _
    exact h_padded
  decides_neg := by
    rintro ⟨N, a⟩ h_no_zero
    have h_a_all : ∀ v ∈ a, 0 < v := fun v hv => by
      by_contra h_v_not_pos
      have h_v_zero : v = 0 := Nat.eq_zero_of_not_pos h_v_not_pos
      exact h_no_zero (h_v_zero ▸ hv)
    have h_enc_eq : encodeAssgn a = (a.map oneVarChunk).flatten ++ [0] :=
      encodeAssgn_nonzero_eq a h_a_all
    set L_cnf := (encodeCnf N).length with hL_cnf
    set L_walk := (a.map oneVarChunk).flatten.length with hL_walk
    -- Phase 1: scan CNF.
    have h_scan := run_scan_to_assgn_start N a
    -- Phase 2: walk a from state 1.
    have h_match : ∀ k (h_k : k < L_walk),
        ∃ (h : L_cnf + k < (encodeInput (N, a)).length),
          (encodeInput (N, a)).get ⟨L_cnf + k, h⟩ =
            ((a.map oneVarChunk).flatten).get ⟨k, h_k⟩ := by
      intro k h_k
      show ∃ (h : L_cnf + k < (encodeCnf N ++ encodeAssgn a).length),
          (encodeCnf N ++ encodeAssgn a).get ⟨L_cnf + k, h⟩ =
            ((a.map oneVarChunk).flatten).get ⟨k, h_k⟩
      rw [h_enc_eq]
      have h_lt_walk : k < ((a.map oneVarChunk).flatten ++ [0]).length := by
        rw [List.length_append, List.length_singleton]
        exact Nat.lt_succ_of_lt h_k
      have h_lt_full : L_cnf + k <
          (encodeCnf N ++ ((a.map oneVarChunk).flatten ++ [0])).length := by
        rw [List.length_append]; exact Nat.add_lt_add_left h_lt_walk _
      refine ⟨h_lt_full, ?_⟩
      rw [List.get_eq_getElem]
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.get_eq_getElem]
      exact List.getElem_append_left h_k
    have h_walk := TM_run_walk_nonzero_assgn a h_a_all []
      (encodeInput (N, a)) L_cnf h_match
    -- Phase 3: read 0 at position L_cnf + L_walk → state 4 (reject).
    have h_0_pos : L_cnf + L_walk < (encodeInput (N, a)).length := by
      show L_cnf + L_walk < (encodeCnf N ++ encodeAssgn a).length
      rw [List.length_append, h_enc_eq, List.length_append, List.length_singleton]
      exact Nat.add_lt_add_left (Nat.lt_succ_self _) _
    have h_get_0 : (encodeInput (N, a))[L_cnf + L_walk]'h_0_pos = 0 := by
      rcases encodeAssgn_get_at_walk_length_nonzero a h_a_all with ⟨_, h_get_walk⟩
      show (encodeCnf N ++ encodeAssgn a)[L_cnf + L_walk]'h_0_pos = 0
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      exact h_get_walk
    have h_step_reject := TM_step_s1_reject_0 [] (encodeInput (N, a))
      (L_cnf + L_walk) h_0_pos h_get_0
    have h_scan_walk := CnfHasEmptyClause.runFlatTM_compose TM L_cnf L_walk _ _ h_scan
    rw [h_walk] at h_scan_walk
    have h_mid_not_halt : haltingStateReached TM
        { state_idx := 1,
          tapes := [([], L_cnf + L_walk, encodeInput (N, a))] } = false := rfl
    have h_chain := AssgnEmpty.runFlatTM_extend_by_step TM (L_cnf + L_walk) _ _ _
      h_scan_walk h_mid_not_halt h_step_reject
    have h_final_halt : haltingStateReached TM
        { state_idx := 4,
          tapes := [([], L_cnf + L_walk, encodeInput (N, a))] } = true := rfl
    have h_walk_plus_one : L_walk + 1 = (encodeAssgn a).length := by
      rw [h_enc_eq, List.length_append, List.length_singleton]
    have h_total_len : L_cnf + (encodeAssgn a).length = (encodeInput (N, a)).length := by
      show (encodeCnf N).length + (encodeAssgn a).length =
        (encodeCnf N ++ encodeAssgn a).length
      rw [List.length_append]
    have h_input_le : (encodeInput (N, a)).length ≤ encodable.size (N, a) + 1 :=
      encodeInput_length_le N a
    have h_le : L_cnf + L_walk + 1 ≤ encodable.size (N, a) + 2 := by
      have h_eq : L_cnf + L_walk + 1 = L_cnf + (encodeAssgn a).length := by
        rw [Nat.add_assoc, h_walk_plus_one]
      have h1 : L_cnf + L_walk + 1 ≤ (encodeInput (N, a)).length := by
        rw [h_eq, h_total_len]
      have h2 : L_cnf + L_walk + 1 ≤ encodable.size (N, a) + 1 :=
        Nat.le_trans h1 h_input_le
      exact Nat.le_trans h2 (Nat.le_succ _)
    rcases Nat.le.dest h_le with ⟨k, h_k⟩
    have h_padded := TMPrimitives.runFlatTM_extend h_chain h_final_halt (k := k)
    rw [h_k] at h_padded
    refine ⟨_, ?_, h_final_halt, rfl⟩
    show runFlatTM (encodable.size (N, a) + 2) TM
        (initFlatConfig TM (initialTapes TM (encodeInput (N, a)))) = _
    show runFlatTM (encodable.size (N, a) + 2) TM
        { state_idx := 0, tapes := [([], 0, encodeInput (N, a))] } = _
    exact h_padded

/-- "The assignment contains a zero entry" is in TM-backed polynomial time. -/
theorem inTimePolyTM_assgnContainsZero :
    inTimePolyTM (fun Na : cnf × assgn => 0 ∈ Na.2) :=
  ⟨fun n => n + 2, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end AssgnContainsZero

/-! ### 6.0p — `AssgnContainsVar v`: parameterized variable lookup

A *family* of TMs `TM (v : Nat)`, each deciding `v ∈ Na.2`. This
generalizes `AssgnContainsZero` (which hardcoded `v = 0`) and is the
prototype for **per-literal variable lookup** in `evalCnfTM`.

State design (state count is `v + 5`, depends on the parameter):
- State `0`           — scanning CNF; on `5` advance to chunk start
- State `k+1`,
  `0 ≤ k < v`         — inside a chunk; have seen `k` 1's; need `v-k`
                        more 1's plus a `6` to accept
- State `v+1`         — *ready*: count = v; accept on next `6`
- State `v+2`         — *overflow*: count > v in current chunk; skip to
                        next chunk on `6`
- State `v+3`         — accept (halting)
- State `v+4`         — reject (halting)

Note the natural decomposition: per-k entries split into the *normal*
case (`k < v`, count strictly below threshold) and the special *ready*
case (`k = v`). This avoids `if k = v` branches in the entry list and
keeps the validity proof straight. -/

namespace AssgnContainsVar

def TM (v : Nat) : FlatTM where
  sig := sigSAT
  tapes := 1
  states := v + 5
  trans :=
    let s0_advance_5 : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_none : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [none], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sready_accept_6 : FlatTMTransEntry :=
      { src_state := v + 1, src_tape_vals := [some 6], dst_state := v + 3,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sready_overflow_1 : FlatTMTransEntry :=
      { src_state := v + 1, src_tape_vals := [some 1], dst_state := v + 2,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let sready_reject_none : FlatTMTransEntry :=
      { src_state := v + 1, src_tape_vals := [none], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sov_one : FlatTMTransEntry :=
      { src_state := v + 2, src_tape_vals := [some 1], dst_state := v + 2,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let sov_six : FlatTMTransEntry :=
      { src_state := v + 2, src_tape_vals := [some 6], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let sov_reject_none : FlatTMTransEntry :=
      { src_state := v + 2, src_tape_vals := [none], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let s0_continue (x : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some x], dst_state := 0,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let s0_reject_symbol (x : Nat) : FlatTMTransEntry :=
      { src_state := 0, src_tape_vals := [some x], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sready_reject_symbol (x : Nat) : FlatTMTransEntry :=
      { src_state := v + 1, src_tape_vals := [some x], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sov_reject_symbol (x : Nat) : FlatTMTransEntry :=
      { src_state := v + 2, src_tape_vals := [some x], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sk_one (k : Nat) : FlatTMTransEntry :=
      { src_state := k + 1, src_tape_vals := [some 1], dst_state := k + 2,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let sk_six (k : Nat) : FlatTMTransEntry :=
      { src_state := k + 1, src_tape_vals := [some 6], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] }
    let sk_reject_none (k : Nat) : FlatTMTransEntry :=
      { src_state := k + 1, src_tape_vals := [none], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    let sk_reject_symbol (k : Nat) (x : Nat) : FlatTMTransEntry :=
      { src_state := k + 1, src_tape_vals := [some x], dst_state := v + 4,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] }
    s0_advance_5 :: s0_reject_none ::
    sready_accept_6 :: sready_overflow_1 :: sready_reject_none ::
    sov_one :: sov_six :: sov_reject_none ::
      (((List.range sigSAT).filter
            (fun x => decide (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4))).map s0_continue ++
        ((List.range sigSAT).filter
            (fun x => decide (x = 0 ∨ x = 6))).map s0_reject_symbol ++
        ((List.range sigSAT).filter
            (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map sready_reject_symbol ++
        ((List.range sigSAT).filter
            (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map sov_reject_symbol ++
        (List.range v).map sk_one ++
        (List.range v).map sk_six ++
        (List.range v).map sk_reject_none ++
        ((List.range v).flatMap (fun k =>
          ((List.range sigSAT).filter
              (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map (sk_reject_symbol k))))
  start := 0
  halt := List.replicate (v + 3) false ++ [true, true]

theorem TM_states (v : Nat) : (TM v).states = v + 5 := rfl

theorem TM_halt_length (v : Nat) : (TM v).halt.length = v + 5 := by
  show (List.replicate (v + 3) false ++ [true, true]).length = v + 5
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_singleton]

theorem TM_valid (v : Nat) : validFlatTM (TM v) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < v + 5; omega
  · exact TM_halt_length v
  · intro entry hentry
    show flatTMTransEntryValid (TM v) entry
    -- Eight explicit prefix entries.
    rcases List.mem_cons.mp hentry with h | h1
    · subst h  -- s0_advance_5
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < v + 5; omega
      · show 1 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([some 5] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 5 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h1 with h | h2
    · subst h  -- s0_reject_none
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h2 with h | h3
    · subst h  -- sready_accept_6
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 1 < v + 5; omega
      · show v + 3 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([some 6] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 6 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h3 with h | h4
    · subst h  -- sready_overflow_1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 1 < v + 5; omega
      · show v + 2 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([some 1] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 1 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h4 with h | h5
    · subst h  -- sready_reject_none
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 1 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h5 with h | h6
    · subst h  -- sov_one
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 2 < v + 5; omega
      · show v + 2 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([some 1] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 1 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h6 with h | h7
    · subst h  -- sov_six
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 2 < v + 5; omega
      · show 1 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([some 6] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; show 6 < sigSAT; decide
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    rcases List.mem_cons.mp h7 with h | hAppend
    · subst h  -- sov_reject_none
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 2 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
      · intro x hx; have hx' : x ∈ ([none] : List (Option Nat)) := hx
        rw [List.mem_singleton] at hx'; subst hx'; trivial
    -- `++` is left-associative, so the appended tail parses as
    --   (((((((A1 ++ A2) ++ A3) ++ A4) ++ A5) ++ A6) ++ A7) ++ FlatMap)
    -- and we peel from the right.
    rcases List.mem_append.mp hAppend with hLeft7 | hFlatMap
    rotate_left
    · -- FlatMap block (rightmost): per-k reject-symbol entries.
      rcases List.mem_flatMap.mp hFlatMap with ⟨k, hk_mem, hxmap⟩
      have hklt : k < v := List.mem_range.mp hk_mem
      rcases List.mem_map.mp hxmap with ⟨x, hx_mem, hmk⟩
      subst hmk
      have hxlt : x < sigSAT := List.mem_range.mp (List.mem_filter.mp hx_mem).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show k + 1 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some x] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; exact hxlt
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft7 with hLeft6 | hSkRejNone
    rotate_left
    · -- A7 = sk_reject_none block.
      rcases List.mem_map.mp hSkRejNone with ⟨k, hk_mem, hmk⟩
      subst hmk
      have hklt : k < v := List.mem_range.mp hk_mem
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show k + 1 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft6 with hLeft5 | hSkSix
    rotate_left
    · -- A6 = sk_six block.
      rcases List.mem_map.mp hSkSix with ⟨k, hk_mem, hmk⟩
      subst hmk
      have hklt : k < v := List.mem_range.mp hk_mem
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show k + 1 < v + 5; omega
      · show 1 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some 6] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; show 6 < sigSAT; decide
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft5 with hLeft4 | hSkOne
    rotate_left
    · -- A5 = sk_one block.
      rcases List.mem_map.mp hSkOne with ⟨k, hk_mem, hmk⟩
      subst hmk
      have hklt : k < v := List.mem_range.mp hk_mem
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show k + 1 < v + 5; omega
      · show k + 2 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some 1] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; show 1 < sigSAT; decide
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft4 with hLeft3 | hOvRej
    rotate_left
    · -- A4 = sov_reject_symbol block.
      rcases List.mem_map.mp hOvRej with ⟨x, hx_mem, hmk⟩
      subst hmk
      have hxlt : x < sigSAT := List.mem_range.mp (List.mem_filter.mp hx_mem).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 2 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some x] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; exact hxlt
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft3 with hLeft2 | hReadyRej
    rotate_left
    · -- A3 = sready_reject_symbol block.
      rcases List.mem_map.mp hReadyRej with ⟨x, hx_mem, hmk⟩
      subst hmk
      have hxlt : x < sigSAT := List.mem_range.mp (List.mem_filter.mp hx_mem).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show v + 1 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some x] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; exact hxlt
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    rcases List.mem_append.mp hLeft2 with hS0Cont | hS0Rej
    · -- A1 = s0_continue block.
      rcases List.mem_map.mp hS0Cont with ⟨x, hx_mem, hmk⟩
      subst hmk
      have hxlt : x < sigSAT := List.mem_range.mp (List.mem_filter.mp hx_mem).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < v + 5; omega
      · show 0 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some x] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; exact hxlt
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial
    · -- A2 = s0_reject_symbol block.
      rcases List.mem_map.mp hS0Rej with ⟨x, hx_mem, hmk⟩
      subst hmk
      have hxlt : x < sigSAT := List.mem_range.mp (List.mem_filter.mp hx_mem).1
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < v + 5; omega
      · show v + 4 < v + 5; omega
      · intro y hy; have hy' : y ∈ ([some x] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; exact hxlt
      · intro y hy; have hy' : y ∈ ([none] : List (Option Nat)) := hy
        rw [List.mem_singleton] at hy'; subst hy'; trivial

/-! ### Private entry defs (parametric in `v`, `k`, `x`) -/

private def s0_advance_5_entry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 5], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_none_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [none], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sready_accept_6_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 1, src_tape_vals := [some 6], dst_state := v + 3,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sready_overflow_1_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 1, src_tape_vals := [some 1], dst_state := v + 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def sready_reject_none_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 1, src_tape_vals := [none], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sov_one_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 2, src_tape_vals := [some 1], dst_state := v + 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def sov_six_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 2, src_tape_vals := [some 6], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def sov_reject_none_entry (v : Nat) : FlatTMTransEntry :=
  { src_state := v + 2, src_tape_vals := [none], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def s0_continue_entry (x : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some x], dst_state := 0,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def s0_reject_symbol_entry (v : Nat) (x : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some x], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sready_reject_symbol_entry (v : Nat) (x : Nat) : FlatTMTransEntry :=
  { src_state := v + 1, src_tape_vals := [some x], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sov_reject_symbol_entry (v : Nat) (x : Nat) : FlatTMTransEntry :=
  { src_state := v + 2, src_tape_vals := [some x], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sk_one_entry (k : Nat) : FlatTMTransEntry :=
  { src_state := k + 1, src_tape_vals := [some 1], dst_state := k + 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def sk_six_entry (k : Nat) : FlatTMTransEntry :=
  { src_state := k + 1, src_tape_vals := [some 6], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

private def sk_reject_none_entry (v : Nat) (k : Nat) : FlatTMTransEntry :=
  { src_state := k + 1, src_tape_vals := [none], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

private def sk_reject_symbol_entry (v : Nat) (k : Nat) (x : Nat) : FlatTMTransEntry :=
  { src_state := k + 1, src_tape_vals := [some x], dst_state := v + 4,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

theorem TM_trans_eq (v : Nat) :
    (TM v).trans =
      s0_advance_5_entry :: s0_reject_none_entry v ::
      sready_accept_6_entry v :: sready_overflow_1_entry v :: sready_reject_none_entry v ::
      sov_one_entry v :: sov_six_entry v :: sov_reject_none_entry v ::
        (((List.range sigSAT).filter
              (fun x => decide (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4))).map s0_continue_entry ++
          ((List.range sigSAT).filter
              (fun x => decide (x = 0 ∨ x = 6))).map (s0_reject_symbol_entry v) ++
          ((List.range sigSAT).filter
              (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map
                (sready_reject_symbol_entry v) ++
          ((List.range sigSAT).filter
              (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map
                (sov_reject_symbol_entry v) ++
          (List.range v).map sk_one_entry ++
          (List.range v).map sk_six_entry ++
          (List.range v).map (sk_reject_none_entry v) ++
          ((List.range v).flatMap (fun k =>
            ((List.range sigSAT).filter
                (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map
                  (sk_reject_symbol_entry v k)))) := rfl

/-! ### `applyTransitionEntry` helpers (Nmove / Rmove on a single tape).

These are the same shape as the helpers in earlier deciders, with the
state and the symbol left abstract. -/

private theorem applyEntry_Nmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Nmove] } =
      some { state_idx := new_state, tapes := [(left, head, right)] } := rfl

private theorem applyEntry_Rmove
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [TMMove.Rmove] } =
      some { state_idx := new_state, tapes := [(left, head + 1, right)] } := rfl

/-! ### Step lemmas

For each (state, symbol-class) pair the TM enters during a successful
run, we prove `stepFlatTM TM { … }` reduces to the right successor
configuration. The pattern mirrors `AssgnContainsZero`'s step lemmas. -/

/-- Generic find? helper for parametric per-k blocks: when an entry of
`(List.range n).map f` matches at exactly index `k₀ < n` (with all
strictly earlier indices not matching), find? returns `some (f k₀)`. -/
private theorem find_range_map_entry_at (n k₀ : Nat) (f : Nat → FlatTMTransEntry)
    (cfg : FlatTMConfig) (h_k₀ : k₀ < n)
    (h_match : entryMatchesConfig (f k₀) cfg = true)
    (h_no_earlier : ∀ k', k' < k₀ → entryMatchesConfig (f k') cfg = false) :
    ((List.range n).map f).find?
      (fun e => entryMatchesConfig e cfg) = some (f k₀) := by
  induction n with
  | zero => exact absurd h_k₀ (Nat.not_lt_zero _)
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          List.find?_append]
      by_cases h_k_eq : k₀ = n
      · -- k₀ = n: prefix returns none, the [f n] returns some (f n).
        have h_pre_none : ((List.range n).map f).find?
            (fun e => entryMatchesConfig e cfg) = none := by
          rw [List.find?_eq_none]
          intro x hx hgood
          rcases List.mem_map.mp hx with ⟨k', hk', rfl⟩
          have hk'_lt_n : k' < n := List.mem_range.mp hk'
          have hk'_lt_k₀ : k' < k₀ := h_k_eq ▸ hk'_lt_n
          have hbad : entryMatchesConfig (f k') cfg = false := h_no_earlier k' hk'_lt_k₀
          rw [hbad] at hgood; exact Bool.false_ne_true hgood
        rw [h_pre_none, Option.none_or]
        have h_n_match : entryMatchesConfig (f n) cfg = true := h_k_eq ▸ h_match
        rw [List.find?_cons, h_n_match, h_k_eq]
      · -- k₀ ≠ n; with k₀ < n+1, get k₀ < n; use IH.
        have h_k₀_lt_n : k₀ < n := by omega
        have h_pre : ((List.range n).map f).find?
            (fun e => entryMatchesConfig e cfg) = some (f k₀) :=
          ih h_k₀_lt_n
        rw [h_pre]; rfl

/-- Convenience: `Nat.beq a b = false` from `a ≠ b`. -/
private theorem nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hbeq : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hbeq) h

/-- If the entry's source state differs from the configuration's state,
the entry doesn't match. -/
private theorem entry_state_ne_no_match {entry : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h : entry.src_state ≠ cfg.state_idx) :
    entryMatchesConfig entry cfg = false := by
  unfold entryMatchesConfig
  cases hbeq : entry.src_state == cfg.state_idx
  · rfl
  · exact absurd (by simpa using hbeq) h

/-- State 0, sym = `some 5`: advance to state 1, head + 1. -/
theorem TM_step_s0_advance_5 (v : Nat)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 5) :
    stepFlatTM (TM v) { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 5 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 5
    rw [dif_pos h_head_lt, h_get]
  have hMatch : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry _ s0_advance_5_entry = _
  exact applyEntry_Rmove 0 1 left right head (some 5)

/-- Find the `s0_continue_entry v` in the filter block when `v ∈ {1,2,3,4}`. -/
private theorem find_s0_continue_match (v_param : Nat)
    (left right : List Nat) (head : Nat) (v : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_v_in : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4) :
    (((List.range sigSAT).filter
          (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4))).map s0_continue_entry).find?
      (fun entry => entryMatchesConfig entry
        { state_idx := 0, tapes := [(left, head, right)] }) =
      some (s0_continue_entry v) := by
  let _ := v_param  -- parameter unused; reserved for caller readability
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some v
    rw [dif_pos h_head_lt, h_get]
  have h_v_lt : v < sigSAT := by rcases h_v_in with h | h | h | h <;> (rw [h]; decide)
  have hvInFilter :
      v ∈ (List.range sigSAT).filter (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_v_lt, ?_⟩
    exact decide_eq_true h_v_in
  generalize hList : (List.range sigSAT).filter
      (fun w => decide (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4)) = L
  rw [hList] at hvInFilter
  clear hList
  induction L with
  | nil => cases hvInFilter
  | cons w ws ih =>
      show List.find? _ (s0_continue_entry w :: ws.map s0_continue_entry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = true := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = true
          rw [hSym]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNotMatch : entryMatchesConfig (s0_continue_entry w)
            { state_idx := 0, tapes := [(left, head, right)] } = false := by
          show ((0 : Nat) == 0 &&
                  decide (([some w] : List (Option Nat)) =
                    [currentTapeSymbol (left, head, right)])) = false
          rw [hSym]
          have h_ne_some : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1; injection h1 with h2; exact hwv h2
          simp [h_ne_some]
        rw [hNotMatch]
        rcases List.mem_cons.mp hvInFilter with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- Symbol-`x` match helper: when the tape head reads `some x`, the
single-tape entry with `src_state = s`, `src_tape_vals = [some x]`
matches a configuration at state `s` with that tape. -/
private theorem entry_self_state_some_match
    (s x : Nat) (left right : List Nat) (head : Nat)
    (entry : FlatTMTransEntry)
    (h_src_state : entry.src_state = s)
    (h_src_vals : entry.src_tape_vals = [some x])
    (h_sym : currentTapeSymbol (left, head, right) = some x) :
    entryMatchesConfig entry { state_idx := s, tapes := [(left, head, right)] } = true := by
  simp [entryMatchesConfig, h_src_state, h_src_vals, h_sym]

/-- Same as above but for `[none]`. -/
private theorem entry_self_state_none_match
    (s : Nat) (left right : List Nat) (head : Nat)
    (entry : FlatTMTransEntry)
    (h_src_state : entry.src_state = s)
    (h_src_vals : entry.src_tape_vals = [none])
    (h_sym : currentTapeSymbol (left, head, right) = none) :
    entryMatchesConfig entry { state_idx := s, tapes := [(left, head, right)] } = true := by
  simp [entryMatchesConfig, h_src_state, h_src_vals, h_sym]

/-- Helper: at state `s`, tape symbol `some x'`, an entry with the same
`src_state = s` but `src_tape_vals = [some x]` for `x ≠ x'` doesn't match. -/
private theorem entry_self_state_sym_ne_no_match
    (s x x' : Nat) (left right : List Nat) (head : Nat)
    (entry : FlatTMTransEntry)
    (h_src_state : entry.src_state = s)
    (h_src_vals : entry.src_tape_vals = [some x])
    (h_x_ne : x ≠ x')
    (h_sym : currentTapeSymbol (left, head, right) = some x') :
    entryMatchesConfig entry { state_idx := s, tapes := [(left, head, right)] } = false := by
  have h_ne : ([some x] : List (Option Nat)) ≠ [some x'] := by
    intro h; injection h with h1; injection h1 with h2; exact h_x_ne h2
  simp [entryMatchesConfig, h_src_state, h_src_vals, h_sym, h_ne]

/-- Helper: at state `s`, tape symbol `some _`, an entry with the same
`src_state = s` but `src_tape_vals = [none]` doesn't match. -/
private theorem entry_self_state_none_ne_some_no_match
    (s x' : Nat) (left right : List Nat) (head : Nat)
    (entry : FlatTMTransEntry)
    (h_src_state : entry.src_state = s)
    (h_src_vals : entry.src_tape_vals = [none])
    (h_sym : currentTapeSymbol (left, head, right) = some x') :
    entryMatchesConfig entry { state_idx := s, tapes := [(left, head, right)] } = false := by
  have h_ne : ([none] : List (Option Nat)) ≠ [some x'] := by
    intro h; injection h with h1; cases h1
  simp [entryMatchesConfig, h_src_state, h_src_vals, h_sym, h_ne]

/-- State 0, sym ∈ `some {1,2,3,4}`: stay in state 0, head + 1. -/
theorem TM_step_s0_continue (v : Nat)
    (left right : List Nat) (head : Nat) (w : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = w)
    (h_w_in : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4) :
    stepFlatTM (TM v) { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some w := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some w
    rw [dif_pos h_head_lt, h_get]
  have h_ne5 : w ≠ 5 := by rcases h_w_in with h | h | h | h <;> (rw [h]; decide)
  have hNot_advance5 : entryMatchesConfig s0_advance_5_entry
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([some 5] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([some 5] : List (Option Nat)) ≠ [some w] := by
      intro h; injection h with h1; injection h1 with h2; exact h_ne5 h2.symm
    simp [h_ne]
  have hNot_state0_none : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := 0, tapes := [(left, head, right)] } = false := by
    show ((0 : Nat) == 0 &&
            decide (([none] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some w] := by
      intro h; injection h with h1; cases h1
    simp [h_ne]
  -- State-mismatched skips: src_state ∈ {v+1, v+2}, cfg.state_idx = 0.
  have h_sready_accept_6_skip := entry_state_ne_no_match (entry := sready_accept_6_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 1) ≠ 0 by omega)
  have h_sready_overflow_1_skip := entry_state_ne_no_match (entry := sready_overflow_1_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 1) ≠ 0 by omega)
  have h_sready_reject_none_skip := entry_state_ne_no_match (entry := sready_reject_none_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 1) ≠ 0 by omega)
  have h_sov_one_skip := entry_state_ne_no_match (entry := sov_one_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 2) ≠ 0 by omega)
  have h_sov_six_skip := entry_state_ne_no_match (entry := sov_six_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 2) ≠ 0 by omega)
  have h_sov_reject_none_skip := entry_state_ne_no_match (entry := sov_reject_none_entry v)
    (cfg := { state_idx := 0, tapes := [(left, head, right)] })
    (show (v + 2) ≠ 0 by omega)
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := 0, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, hNot_advance5]
  rw [List.find?_cons, hNot_state0_none]
  rw [List.find?_cons, h_sready_accept_6_skip]
  rw [List.find?_cons, h_sready_overflow_1_skip]
  rw [List.find?_cons, h_sready_reject_none_skip]
  rw [List.find?_cons, h_sov_one_skip]
  rw [List.find?_cons, h_sov_six_skip]
  rw [List.find?_cons, h_sov_reject_none_skip]
  -- Now we hit the appended blocks. The s0_continue block is at the front
  -- of the left-deep ((((((((A1 ++ A2) ++ A3) ++ A4) ++ A5) ++ A6) ++ A7) ++ FlatMap).
  -- Peel down to A1 with seven find?_append rewrites.
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append,
      List.find?_append, List.find?_append, List.find?_append]
  rw [find_s0_continue_match v left right head w h_head_lt h_get h_w_in]
  show applyTransitionEntry _ (s0_continue_entry w) = _
  exact applyEntry_Rmove 0 0 left right head (some w)

/-- State v+1, sym = `some 6`: accept (state v+3). -/
theorem TM_step_sready_accept_6 (v : Nat)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM (TM v) { state_idx := v + 1, tapes := [(left, head, right)] } =
      some { state_idx := v + 3, tapes := [(left, head, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 6
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := v + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 1 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := v + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 1 by omega)
  have hMatch : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := v + 1, tapes := [(left, head, right)] } = true :=
    entry_self_state_some_match (v + 1) 6 left right head (sready_accept_6_entry v)
      rfl rfl hSym
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := v + 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ (sready_accept_6_entry v) = _
  exact applyEntry_Nmove (v + 1) (v + 3) left right head (some 6)

/-- State v+1, sym = `some 1`: enter overflow (state v+2). -/
theorem TM_step_sready_overflow_1 (v : Nat)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (TM v) { state_idx := v + 1, tapes := [(left, head, right)] } =
      some { state_idx := v + 2, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 1
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := v + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 1 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := v + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 1 by omega)
  have h_skip3 : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := v + 1, tapes := [(left, head, right)] } = false :=
    entry_self_state_sym_ne_no_match (v + 1) 6 1 left right head
      (sready_accept_6_entry v) rfl rfl (by decide) hSym
  have hMatch : entryMatchesConfig (sready_overflow_1_entry v)
      { state_idx := v + 1, tapes := [(left, head, right)] } = true :=
    entry_self_state_some_match (v + 1) 1 left right head (sready_overflow_1_entry v)
      rfl rfl hSym
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := v + 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, h_skip3]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ (sready_overflow_1_entry v) = _
  exact applyEntry_Rmove (v + 1) (v + 2) left right head (some 1)

/-- State v+2, sym = `some 1`: stay in overflow (state v+2). -/
theorem TM_step_sov_continue_1 (v : Nat)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (TM v) { state_idx := v + 2, tapes := [(left, head, right)] } =
      some { state_idx := v + 2, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 1
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 2 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 2 by omega)
  have h_skip3 : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have h_skip4 : entryMatchesConfig (sready_overflow_1_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have h_skip5 : entryMatchesConfig (sready_reject_none_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have hMatch : entryMatchesConfig (sov_one_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = true :=
    entry_self_state_some_match (v + 2) 1 left right head (sov_one_entry v)
      rfl rfl hSym
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := v + 2, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, h_skip3]
  rw [List.find?_cons, h_skip4]
  rw [List.find?_cons, h_skip5]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ (sov_one_entry v) = _
  exact applyEntry_Rmove (v + 2) (v + 2) left right head (some 1)

/-- Generic helper: if no element of `l` produces a matching entry,
`find?` returns `none`. -/
private theorem find_map_no_match {β : Type _} (l : List β) (f : β → FlatTMTransEntry)
    (cfg : FlatTMConfig)
    (h_no_match : ∀ x ∈ l, entryMatchesConfig (f x) cfg = false) :
    (l.map f).find? (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro y hy hgood
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  rw [h_no_match x hx] at hgood
  exact Bool.false_ne_true hgood

/-- The `s0_continue` filter block has no matching entry when
`cfg.state_idx ≠ 0`. -/
private theorem find_s0_cont_block_no_match (state_idx : Nat) (h : 0 ≠ state_idx)
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun x => decide (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4))).map s0_continue_entry).find?
      (fun e => entryMatchesConfig e
        { state_idx := state_idx, tapes := [(left, head, right)] }) = none := by
  refine find_map_no_match _ _ _ (fun x _ => ?_)
  exact entry_state_ne_no_match h

/-- The `s0_reject_symbol` filter block has no matching entry when
`cfg.state_idx ≠ 0`. -/
private theorem find_s0_rej_block_no_match (v : Nat) (state_idx : Nat) (h : 0 ≠ state_idx)
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun x => decide (x = 0 ∨ x = 6))).map (s0_reject_symbol_entry v)).find?
      (fun e => entryMatchesConfig e
        { state_idx := state_idx, tapes := [(left, head, right)] }) = none := by
  refine find_map_no_match _ _ _ (fun x _ => ?_)
  exact entry_state_ne_no_match h

/-- The `sready_reject_symbol` filter block has no matching entry when
`cfg.state_idx ≠ v + 1`. -/
private theorem find_sready_rej_block_no_match (v : Nat) (state_idx : Nat)
    (h : (v + 1) ≠ state_idx)
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map
            (sready_reject_symbol_entry v)).find?
      (fun e => entryMatchesConfig e
        { state_idx := state_idx, tapes := [(left, head, right)] }) = none := by
  refine find_map_no_match _ _ _ (fun x _ => ?_)
  exact entry_state_ne_no_match h

/-- The `sov_reject_symbol` filter block has no matching entry when
`cfg.state_idx ≠ v + 2`. -/
private theorem find_sov_rej_block_no_match (v : Nat) (state_idx : Nat)
    (h : (v + 2) ≠ state_idx)
    (left right : List Nat) (head : Nat) :
    (((List.range sigSAT).filter
          (fun x => decide (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5))).map
            (sov_reject_symbol_entry v)).find?
      (fun e => entryMatchesConfig e
        { state_idx := state_idx, tapes := [(left, head, right)] }) = none := by
  refine find_map_no_match _ _ _ (fun x _ => ?_)
  exact entry_state_ne_no_match h

/-- State v+2, sym = `some 6`: end overflow, move to next chunk (state 1). -/
theorem TM_step_sov_next_6 (v : Nat)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM (TM v) { state_idx := v + 2, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 6
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 2 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ v + 2 by omega)
  have h_skip3 : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have h_skip4 : entryMatchesConfig (sready_overflow_1_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have h_skip5 : entryMatchesConfig (sready_reject_none_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ v + 2 by omega)
  have h_skip6 : entryMatchesConfig (sov_one_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = false :=
    entry_self_state_sym_ne_no_match (v + 2) 1 6 left right head
      (sov_one_entry v) rfl rfl (by decide) hSym
  have hMatch : entryMatchesConfig (sov_six_entry v)
      { state_idx := v + 2, tapes := [(left, head, right)] } = true :=
    entry_self_state_some_match (v + 2) 6 left right head (sov_six_entry v)
      rfl rfl hSym
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := v + 2, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, h_skip3]
  rw [List.find?_cons, h_skip4]
  rw [List.find?_cons, h_skip5]
  rw [List.find?_cons, h_skip6]
  rw [List.find?_cons, hMatch]
  show applyTransitionEntry _ (sov_six_entry v) = _
  exact applyEntry_Rmove (v + 2) 1 left right head (some 6)

/-- `find?` on the `sk_one` block: when the current symbol is not `1`,
no entry matches (state-matched index has symbol mismatch, state-mismatched
indices skip via `entry_state_ne_no_match`). -/
private theorem find_sk_one_block_no_match_sym_ne
    (v k x' : Nat) (h_x_ne : 1 ≠ x') (left right : List Nat) (head : Nat)
    (h_sym : currentTapeSymbol (left, head, right) = some x') :
    ((List.range v).map sk_one_entry).find?
      (fun e => entryMatchesConfig e
        { state_idx := k + 1, tapes := [(left, head, right)] }) = none := by
  refine find_map_no_match _ _ _ (fun k' _ => ?_)
  by_cases h_k_eq : k' = k
  · subst h_k_eq
    exact entry_self_state_sym_ne_no_match (k' + 1) 1 x' left right head
      (sk_one_entry k') rfl rfl h_x_ne h_sym
  · exact entry_state_ne_no_match (show (k' + 1) ≠ k + 1 by intro h; exact h_k_eq (Nat.succ_inj.mp h))

/-- State k+1 with `k < v`, sym = `some 1`: increment counter to state k+2. -/
theorem TM_step_sk_enter_1 (v k : Nat) (h_k_lt : k < v)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (TM v) { state_idx := k + 1, tapes := [(left, head, right)] } =
      some { state_idx := k + 2, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 1
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ k + 1 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ k + 1 by omega)
  have h_skip3 : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip4 : entryMatchesConfig (sready_overflow_1_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip5 : entryMatchesConfig (sready_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip6 : entryMatchesConfig (sov_one_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_skip7 : entryMatchesConfig (sov_six_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_skip8 : entryMatchesConfig (sov_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_block_s0_cont :=
    find_s0_cont_block_no_match (k + 1) (show 0 ≠ k + 1 by omega) left right head
  have h_block_s0_rej :=
    find_s0_rej_block_no_match v (k + 1) (show 0 ≠ k + 1 by omega) left right head
  have h_block_sready_rej :=
    find_sready_rej_block_no_match v (k + 1) (show (v + 1) ≠ k + 1 by omega) left right head
  have h_block_sov_rej :=
    find_sov_rej_block_no_match v (k + 1) (show (v + 2) ≠ k + 1 by omega) left right head
  have h_sk_one_match :
      ((List.range v).map sk_one_entry).find?
        (fun e => entryMatchesConfig e
          { state_idx := k + 1, tapes := [(left, head, right)] }) =
        some (sk_one_entry k) := by
    refine find_range_map_entry_at v k sk_one_entry _ h_k_lt ?_ ?_
    · exact entry_self_state_some_match (k + 1) 1 left right head (sk_one_entry k)
        rfl rfl hSym
    · intro k' h_k'_lt_k
      exact entry_state_ne_no_match (show (k' + 1) ≠ k + 1 by omega)
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := k + 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, h_skip3]
  rw [List.find?_cons, h_skip4]
  rw [List.find?_cons, h_skip5]
  rw [List.find?_cons, h_skip6]
  rw [List.find?_cons, h_skip7]
  rw [List.find?_cons, h_skip8]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append,
      List.find?_append, List.find?_append, List.find?_append]
  rw [h_block_s0_cont, h_block_s0_rej, h_block_sready_rej, h_block_sov_rej]
  rw [h_sk_one_match]
  -- Or chain: (((((none.or none .or none) .or none) .or some (sk_one_entry k)) .or _) .or _) .or _
  -- collapses to some (sk_one_entry k). Then Option.bind reduces.
  show applyTransitionEntry _ (sk_one_entry k) = _
  exact applyEntry_Rmove (k + 1) (k + 2) left right head (some 1)

/-- State k+1 with `k < v`, sym = `some 6`: end chunk, move to next (state 1). -/
theorem TM_step_sk_next_6 (v k : Nat) (h_k_lt : k < v)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM (TM v) { state_idx := k + 1, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = some 6
    rw [dif_pos h_head_lt, h_get]
  have h_skip1 : entryMatchesConfig s0_advance_5_entry
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ k + 1 by omega)
  have h_skip2 : entryMatchesConfig (s0_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (0 : Nat) ≠ k + 1 by omega)
  have h_skip3 : entryMatchesConfig (sready_accept_6_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip4 : entryMatchesConfig (sready_overflow_1_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip5 : entryMatchesConfig (sready_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 1) ≠ k + 1 by omega)
  have h_skip6 : entryMatchesConfig (sov_one_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_skip7 : entryMatchesConfig (sov_six_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_skip8 : entryMatchesConfig (sov_reject_none_entry v)
      { state_idx := k + 1, tapes := [(left, head, right)] } = false :=
    entry_state_ne_no_match (show (v + 2) ≠ k + 1 by omega)
  have h_block_s0_cont :=
    find_s0_cont_block_no_match (k + 1) (show 0 ≠ k + 1 by omega) left right head
  have h_block_s0_rej :=
    find_s0_rej_block_no_match v (k + 1) (show 0 ≠ k + 1 by omega) left right head
  have h_block_sready_rej :=
    find_sready_rej_block_no_match v (k + 1) (show (v + 1) ≠ k + 1 by omega) left right head
  have h_block_sov_rej :=
    find_sov_rej_block_no_match v (k + 1) (show (v + 2) ≠ k + 1 by omega) left right head
  -- sk_one block: every entry has src_tape_vals = [some 1], but we read 6. No match.
  have h_block_sk_one : ((List.range v).map sk_one_entry).find?
      (fun e => entryMatchesConfig e
        { state_idx := k + 1, tapes := [(left, head, right)] }) = none :=
    find_sk_one_block_no_match_sym_ne v k 6 (by decide) left right head hSym
  -- sk_six block: match at index k.
  have h_sk_six_match :
      ((List.range v).map sk_six_entry).find?
        (fun e => entryMatchesConfig e
          { state_idx := k + 1, tapes := [(left, head, right)] }) =
        some (sk_six_entry k) := by
    refine find_range_map_entry_at v k sk_six_entry _ h_k_lt ?_ ?_
    · exact entry_self_state_some_match (k + 1) 6 left right head (sk_six_entry k)
        rfl rfl hSym
    · intro k' h_k'_lt_k
      exact entry_state_ne_no_match (show (k' + 1) ≠ k + 1 by omega)
  show Option.bind ((TM v).trans.find?
        (fun entry => entryMatchesConfig entry
          { state_idx := k + 1, tapes := [(left, head, right)] }))
      (applyTransitionEntry _) = _
  rw [TM_trans_eq]
  rw [List.find?_cons, h_skip1]
  rw [List.find?_cons, h_skip2]
  rw [List.find?_cons, h_skip3]
  rw [List.find?_cons, h_skip4]
  rw [List.find?_cons, h_skip5]
  rw [List.find?_cons, h_skip6]
  rw [List.find?_cons, h_skip7]
  rw [List.find?_cons, h_skip8]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append,
      List.find?_append, List.find?_append, List.find?_append]
  rw [h_block_s0_cont, h_block_s0_rej, h_block_sready_rej, h_block_sov_rej]
  rw [h_block_sk_one, h_sk_six_match]
  show applyTransitionEntry _ (sk_six_entry k) = _
  exact applyEntry_Rmove (k + 1) 1 left right head (some 6)

end AssgnContainsVar

end SAT_TM
