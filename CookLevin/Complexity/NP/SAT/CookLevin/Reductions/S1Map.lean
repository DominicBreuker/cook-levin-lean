import Complexity.Simulators.GuessTableau
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

/-! # S1, part 1 — the honest reduction MAP `FlatSingleTMGenNP → FlatTCC`

The **mathematical half** of the S1 free witness (the machine half — the `Cmd`
emitting this map — is `S1Witness.lean`). This file fixes the reduction
function, proves it correct, and bounds its output size; the witness file then
only has to *compute* it.

**The guarded-map pattern** (HANDOFF standing risk 3, template
`Reductions/FlatCC_to_BinaryCC_free.lean`). `guessTableau_correct` needs three
hypotheses — `validFlatTM M`, `M.tapes = 1`, `list_ofFlatType M.sig s` — which
are exactly the first three conjuncts of `FlatSingleTMGenNP`. They are
*decidable properties of the input*, so the map may branch on them (legitimate;
this is NOT an if-on-the-answer). Off-guard instances are no-instances on both
sides, so the map sends them to a fixed non-instance `s1No`:

    s1Map (M, s, maxSize, steps) =
      if s1GuardB M s then guessTableau M s maxSize steps else s1No

**Why a guard at all** (the unguarded map is *not* available here, unlike
`FlatTCC → FlatCC`): `guessTableau M s maxSize steps` is a total, honest
function of the instance, but its *correctness* is conditional. For an invalid
`M` the tableau is still built — and it may well be coverable — while
`FlatSingleTMGenNP` is false because of the `validFlatTM` conjunct. So the
unguarded map would be unsound in the backward direction. Checking the guard
on-machine is therefore an obligation of the S1 program, not optional.

**Cost note for the program (`S1Witness.lean`).** The guard is a bounded scan
of the machine register: `M.start < M.states`, `|M.halt| = M.states`, and one
pass over `M.trans` comparing five lengths and two symbol bounds per entry,
plus one pass over `s` checking `< M.sig`. All comparisons are on unary
numbers already present in the head layout's machine register. -/

namespace S1Map

open Complexity.Simulators

/-! ## The decidable guard -/

/-- The per-symbol bound check reflects `flatTMOptionSymbolsBounded`. -/
private theorem optAll_iff (sig : Nat) (l : List (Option Nat)) :
    l.all (isSomeNatBelow sig) = true ↔ flatTMOptionSymbolsBounded sig l := by
  simp only [List.all_eq_true, flatTMOptionSymbolsBounded]
  constructor
  · intro h x hx
    cases x with
    | none => trivial
    | some v => simpa [isSomeNatBelow] using h _ hx
  · intro h x hx
    cases x with
    | none => rfl
    | some v => simpa [isSomeNatBelow] using h _ hx

/-- The per-entry check reflects `flatTMTransEntryValid`. -/
private theorem entryB_iff (M : flatTM) (e : FlatTMTransEntry) :
    (decide (e.src_state < M.states) &&
      decide (e.dst_state < M.states) &&
      decide (e.src_tape_vals.length = M.tapes) &&
      decide (e.dst_write_vals.length = M.tapes) &&
      decide (e.move_dirs.length = M.tapes) &&
      e.src_tape_vals.all (isSomeNatBelow M.sig) &&
      e.dst_write_vals.all (isSomeNatBelow M.sig)) = true
      ↔ flatTMTransEntryValid M e := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, optAll_iff, flatTMTransEntryValid]
  tauto

/-- `isValidFlatTM` reflects `validFlatTM`. (The `Bool` twin existed; the
reflection lemma did not.) -/
theorem isValidFlatTM_iff (M : flatTM) : isValidFlatTM M = true ↔ validFlatTM M := by
  unfold isValidFlatTM validFlatTM
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.all_eq_true]
  simp only [entryB_iff]
  tauto

/-- The full S1 guard as a `Bool`: the three decidable instance-validity
conjuncts of `FlatSingleTMGenNP` — exactly `guessTableau_correct`'s
hypotheses. -/
def s1GuardB (M : flatTM) (s : List Nat) : Bool :=
  isValidFlatTM M && decide (M.tapes = 1) && s.all (fun x => decide (x < M.sig))

theorem s1GuardB_iff (M : flatTM) (s : List Nat) :
    s1GuardB M s = true ↔
      (validFlatTM M ∧ M.tapes = 1 ∧ list_ofFlatType M.sig s) := by
  unfold s1GuardB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    isValidFlatTM_iff]
  constructor
  · rintro ⟨⟨hV, hT⟩, hs⟩
    exact ⟨hV, hT, fun x hx => hs x hx⟩
  · rintro ⟨hV, hT, hs⟩
    exact ⟨⟨hV, hT⟩, fun x hx => hs x hx⟩

/-! ## The off-guard image

`FlatTCC_wellformed C := C.init.length ≥ 3`, so the empty word is the cheapest
possible non-instance — and it is also the cheapest possible thing for the
program to emit (five empty registers). -/

/-- The fixed no-instance: not `FlatTCC_wellformed`, hence not in the
language, whatever its other fields say. -/
def s1No : FlatTCC where
  Sigma := 0
  init := []
  cards := []
  final := []
  steps := 0

theorem s1No_not_lang : ¬ FlatTCC.FlatTCCLang s1No := by
  rintro ⟨hwf, -⟩
  simp [FlatTCC.FlatTCC_wellformed, s1No] at hwf

/-! ## The map and its correctness -/

/-- **The honest S1 reduction map.** A genuine computable function of the
instance; the branch tests a decidable property of the *input*, never the
source predicate's truth. -/
def s1Map : flatTM × List Nat × Nat × Nat → FlatTCC
  | (M, s, maxSize, steps) =>
      if s1GuardB M s then guessTableau M s maxSize steps else s1No

/-- Yes-branch equation (the `match` does not reduce under `unfold`). -/
theorem s1Map_pos (M : flatTM) (s : List Nat) (mx st : Nat)
    (hg : s1GuardB M s = true) : s1Map (M, s, mx, st) = guessTableau M s mx st := by
  show (if s1GuardB M s = true then guessTableau M s mx st else s1No) = _
  simp [hg]

/-- No-branch equation. -/
theorem s1Map_neg (M : flatTM) (s : List Nat) (mx st : Nat)
    (hg : ¬ s1GuardB M s = true) : s1Map (M, s, mx, st) = s1No := by
  show (if s1GuardB M s = true then guessTableau M s mx st else s1No) = _
  simp [hg]

/-- **The S1 reduction is correct.** Consumes `guessTableau_correct` as a black
box; the guard supplies its three hypotheses on the yes-branch and kills both
sides on the no-branch. -/
theorem s1Map_correct (x : flatTM × List Nat × Nat × Nat) :
    FlatSingleTMGenNP x ↔ FlatTCC.FlatTCCLang (s1Map x) := by
  obtain ⟨M, s, maxSize, steps⟩ := x
  by_cases hg : s1GuardB M s = true
  · rw [s1Map_pos M s maxSize steps hg]
    obtain ⟨hV, hT, hs⟩ := (s1GuardB_iff M s).1 hg
    rw [← guessTableau_correct M s maxSize steps hV hT hs]
    unfold FlatSingleTMGenNP
    constructor
    · rintro ⟨-, -, -, hcert⟩; exact hcert
    · intro hcert; exact ⟨hV, hT, hs, hcert⟩
  · rw [s1Map_neg M s maxSize steps hg]
    constructor
    · rintro ⟨hV, hT, hs, -⟩
      exact absurd ((s1GuardB_iff M s).2 ⟨hV, hT, hs⟩) hg
    · intro h; exact absurd h s1No_not_lang

/-! ## Output size

`guessTableau_size_bound` is stated in the tableau's own parameters; here it is
re-expressed in `encodable.size` of the instance — the shape
`PolyTimeComputableLang.output_size_le` wants. -/

/-- Every parameter the tableau's size bound scales in is dominated by the
instance's `encodable.size`. **This needs the honest `encodable FlatTM`**
(2026-07-25): under the former flat-`5`-per-entry measure `M.trans.length` was
dominated but the entry payloads were not — see `Definitions.lean`. -/
theorem s1_param_le (M : flatTM) (s : List Nat) (maxSize steps : Nat) :
    s.length + maxSize + steps + M.sig + M.states + M.trans.length
      ≤ encodable.size ((M, s, maxSize, steps) : flatTM × List Nat × Nat × Nat) := by
  have hs : s.length ≤ encodable.size s := by
    show s.length ≤ s.foldl (fun acc x => acc + encodable.size x + 1) 0
    have : ∀ (l : List Nat) (a : Nat),
        a + l.length ≤ l.foldl (fun acc x => acc + encodable.size x + 1) a := by
      intro l
      induction l with
      | nil => intro a; simp
      | cons y ys ih =>
          intro a
          have := ih (a + encodable.size y + 1)
          simp only [List.foldl_cons, List.length_cons]
          omega
    simpa using this s 0
  have ht : M.trans.length ≤ encodable.size M.trans := by
    show M.trans.length ≤ M.trans.foldl (fun acc x => acc + encodable.size x + 1) 0
    have : ∀ (l : List FlatTMTransEntry) (a : Nat),
        a + l.length ≤ l.foldl (fun acc x => acc + encodable.size x + 1) a := by
      intro l
      induction l with
      | nil => intro a; simp
      | cons y ys ih =>
          intro a
          have := ih (a + encodable.size y + 1)
          simp only [List.foldl_cons, List.length_cons]
          omega
    simpa using this M.trans 0
  have hprod : encodable.size ((M, s, maxSize, steps) : flatTM × List Nat × Nat × Nat)
      = encodable.size M + (encodable.size s + (maxSize + steps + 1) + 1) + 1 := rfl
  have hM : encodable.size M
      = M.sig + M.tapes + M.states + M.start
        + encodable.size M.halt + encodable.size M.trans + 1 := rfl
  omega

/-- The `output_size_le` polynomial: `(2·(n+3))^10`. -/
def s1Bound (n : Nat) : Nat := (2 * (n + 3)) ^ 10

theorem s1Bound_mono : monotonic s1Bound := by
  intro a b h
  exact Nat.pow_le_pow_left (by omega) 10

theorem s1Bound_poly : inOPoly s1Bound := by
  refine ⟨10, 8 ^ 10, 1, ?_⟩
  intro n hn
  show (2 * (n + 3)) ^ 10 ≤ 8 ^ 10 * n ^ 10
  calc (2 * (n + 3)) ^ 10 ≤ (8 * n) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    _ = 8 ^ 10 * n ^ 10 := by rw [Nat.mul_pow]

/-- **The S1 output-size bound**, in the witness field's shape. -/
theorem s1Map_size_le (x : flatTM × List Nat × Nat × Nat) :
    encodable.size (s1Map x) ≤ s1Bound (encodable.size x) := by
  obtain ⟨M, s, maxSize, steps⟩ := x
  unfold s1Bound
  by_cases hg : s1GuardB M s = true
  · rw [s1Map_pos M s maxSize steps hg]
    refine le_trans (guessTableau_size_bound M s maxSize steps) ?_
    exact Nat.pow_le_pow_left (by have := s1_param_le M s maxSize steps; omega) 10
  · rw [s1Map_neg M s maxSize steps hg]
    have h1 : encodable.size s1No = 1 := rfl
    have h2 : 1 ≤ (2 * (encodable.size ((M, s, maxSize, steps) :
        flatTM × List Nat × Nat × Nat) + 3)) ^ 10 :=
      Nat.one_le_pow _ _ (by omega)
    omega

end S1Map
