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
private theorem runFlatTM_extend_by_step
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

end SAT_TM
