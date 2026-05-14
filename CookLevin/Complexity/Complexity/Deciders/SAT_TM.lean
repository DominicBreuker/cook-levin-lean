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

end SAT_TM
