import Complexity.Complexity.NP
import Complexity.NP.kSAT
import Complexity.NP.FlatClique

set_option autoImplicit false
open Classical

------------------------------------------------------------------------
-- §1  Clause positions
------------------------------------------------------------------------

def clausePositionsAux : List clause → Nat → List (Nat × Nat)
  | [], _ => []
  | C :: Cs, ci =>
      (List.range C.length).map (fun li => (ci, li)) ++ clausePositionsAux Cs (ci + 1)

def clausePositions (N : cnf) : List (Nat × Nat) :=
  clausePositionsAux N 0

------------------------------------------------------------------------
-- §2  Literal access
------------------------------------------------------------------------

def nthClause : List clause → Nat → Option clause
  | [], _ => none
  | C :: _, 0 => some C
  | _ :: Cs, n + 1 => nthClause Cs n

def nthLiteral : clause → Nat → Option literal
  | [], _ => none
  | l :: _, 0 => some l
  | _ :: C, n + 1 => nthLiteral C n

def literalAt (N : cnf) (ci li : Nat) : Option literal := do
  let C ← nthClause N ci
  nthLiteral C li

def literalPolarity (l : literal) : Bool := l.1

def literalVar (l : literal) : Nat := l.2

def literalsAreNegations (l₁ l₂ : literal) : Bool :=
  literalVar l₁ == literalVar l₂ && literalPolarity l₁ != literalPolarity l₂

------------------------------------------------------------------------
-- §3  Position compatibility and encoding
------------------------------------------------------------------------

def positionCompatible (N : cnf) (p q : Nat × Nat) : Bool :=
  p.1 != q.1 &&
    match literalAt N p.1 p.2, literalAt N q.1 q.2 with
    | some l₁, some l₂ => !(literalsAreNegations l₁ l₂)
    | _, _ => false

def positionBase (N : cnf) : Nat :=
  (N.foldr (fun C acc => Nat.max C.length acc) 0) + 1

def encodePosition (N : cnf) (p : Nat × Nat) : Nat :=
  p.1 * positionBase N + p.2

def addCompatibleEdges (N : cnf) (positions : List (Nat × Nat)) (p : Nat × Nat) :
    List fedge :=
  (positions.filter (positionCompatible N p)).map
    (fun q => (encodePosition N p, encodePosition N q))

def cliqueVertices (N : cnf) : List Nat :=
  (clausePositions N).map (encodePosition N)

def cliqueEdges (N : cnf) : List fedge :=
  let positions := clausePositions N
  positions.flatMap (addCompatibleEdges N positions)

------------------------------------------------------------------------
-- §4  The reduction
------------------------------------------------------------------------

/-- The Karp reduction graph.  Vertices 0 .. N.length * positionBase N - 1
    encode clause-literal positions; the k-clique size is N.length. -/
def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  ((N.length * positionBase N, cliqueEdges N), N.length)

/-- Trivial no-instance: vertex bound 0 forces list_ofFlatType to be vacuously
    false for any non-empty list, so the required 1-clique cannot exist. -/
private def noCliqueInstance : fgraph × Nat := ((0, []), 1)

/-- Guarded reduction: applies the Karp construction on valid k-CNF inputs,
    maps everything else to the no-instance. -/
private def kSAT_to_FlatClique_f (k : Nat) (N : cnf) : fgraph × Nat :=
  if 0 < k ∧ kCNF k N then kSAT_to_FlatClique_instance N else noCliqueInstance

------------------------------------------------------------------------
-- §5  nthClause / nthLiteral agree with List.get?
------------------------------------------------------------------------

private theorem nthClause_eq_get? : ∀ (N : cnf) (i : Nat), nthClause N i = N.get? i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: Cs, n + 1 => nthClause_eq_get? Cs n

private theorem nthLiteral_eq_get? : ∀ (C : clause) (i : Nat), nthLiteral C i = C.get? i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: C, n + 1 => nthLiteral_eq_get? C n

private theorem literalAt_eq (N : cnf) (ci li : Nat) :
    literalAt N ci li = (N.get? ci).bind (fun C => C.get? li) := by
  simp [literalAt, nthClause_eq_get?, nthLiteral_eq_get?, Option.bind]

------------------------------------------------------------------------
-- §6  get? / getD utility lemmas
------------------------------------------------------------------------

/-- When n < l.length, l.get? n = some (l.getD n d). -/
private theorem get?_eq_some_getD {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.get? n = some (l.getD n d) := by
  induction l generalizing n with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [List.getD] using ih (by simpa using h)

/-- When n < l.length, l.getD n d equals the element l.get ⟨n, h⟩. -/
private theorem getD_eq_get {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d = l.get ⟨n, h⟩ := by
  induction l generalizing n with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [List.getD, List.get] using ih (by simpa using h)

/-- When n < l.length, l.getD n d is a member of l. -/
private theorem getD_mem {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d ∈ l := by
  rw [getD_eq_get l n d h]
  exact List.get_mem l n h

/-- For any nonempty clause, there is a satisfied literal index when
    the clause is satisfied by an assignment. -/
private theorem any_to_exists_index (l : clause) (p : literal → Bool)
    (h : l.any p = true) :
    ∃ i, i < l.length ∧ p (l.getD i (true, 0)) = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with hx | hxs
    · exact ⟨0, Nat.zero_lt_succ _, by simp [List.getD, hx]⟩
    · obtain ⟨i, hi, hpi⟩ := ih hxs
      exact ⟨i + 1, Nat.succ_lt_succ hi, by simp [List.getD, hpi]⟩

------------------------------------------------------------------------
-- §7  clausePositions membership
------------------------------------------------------------------------

/-- Membership in clausePositionsAux: (ci, li) iff
    base ≤ ci, ci - base < N.length, and li < (N.getD (ci-base) []).length. -/
private theorem clausePositionsAux_mem (N : cnf) (base : Nat) (ci li : Nat) :
    (ci, li) ∈ clausePositionsAux N base ↔
    base ≤ ci ∧ ci - base < N.length ∧ li < (N.getD (ci - base) []).length := by
  induction N generalizing base ci with
  | nil => simp [clausePositionsAux]
  | cons C Cs ih =>
    simp only [clausePositionsAux, List.mem_append, List.mem_map, List.mem_range,
               List.length_cons]
    constructor
    · rintro (⟨li', hli', hpair⟩ | hmem)
      · obtain ⟨hci, hli⟩ : ci = base ∧ li = li' := by
          simp [Prod.mk.injEq] at hpair; exact ⟨hpair.1, hpair.2⟩
        subst hci hli
        exact ⟨le_refl _, by simp, by simp [List.getD]; exact hli'⟩
      · obtain ⟨hle, hlen, hliD⟩ := (ih (base + 1) ci li).mp hmem
        refine ⟨Nat.le_trans (Nat.le_succ _) hle, ?_, ?_⟩
        · have : ci - base = ci - (base + 1) + 1 := by omega
          simp [this]; exact hlen
        · have hcibig : ci - base = ci - (base + 1) + 1 := by omega
          rw [hcibig]; simp [List.getD]; exact hliD
    · rintro ⟨hle, hlen, hliD⟩
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · simp at hlen hliD
        left; exact ⟨li, hliD, rfl⟩
      · right
        rw [ih (base + 1) ci li]
        refine ⟨hlt, ?_, ?_⟩
        · have : ci - base = ci - (base + 1) + 1 := by omega
          rw [this] at hlen; simpa using hlen
        · have : ci - base = ci - (base + 1) + 1 := by omega
          rw [this] at hliD; simpa [List.getD] using hliD

/-- (ci, li) ∈ clausePositions N iff ci < N.length and
    li < the length of clause ci. -/
private theorem clausePositions_mem (N : cnf) (ci li : Nat) :
    (ci, li) ∈ clausePositions N ↔
    ci < N.length ∧ li < (N.getD ci []).length := by
  simp only [clausePositions, clausePositionsAux_mem N 0 ci li]
  omega

/-- A valid clause position yields a non-None literalAt. -/
private theorem clausePositions_literalAt_some (N : cnf) (ci li : Nat)
    (h : (ci, li) ∈ clausePositions N) : ∃ l, literalAt N ci li = some l := by
  obtain ⟨hci, hli⟩ := (clausePositions_mem N ci li).mp h
  rw [literalAt_eq, get?_eq_some_getD N ci [] hci,
      get?_eq_some_getD (N.getD ci []) li (true, 0) hli]
  exact ⟨_, rfl⟩

------------------------------------------------------------------------
-- §8  positionBase bounds
------------------------------------------------------------------------

/-- positionBase is always positive. -/
private theorem positionBase_pos (N : cnf) : 0 < positionBase N :=
  Nat.succ_pos _

/-- Every clause length is strictly below positionBase N. -/
private theorem positionBase_gt_clauseLen (N : cnf) (C : clause) (hC : C ∈ N) :
    C.length < positionBase N := by
  simp only [positionBase]
  suffices h : C.length ≤ N.foldr (fun D acc => Nat.max D.length acc) 0 by omega
  induction N with
  | nil => exact absurd hC (List.not_mem_nil _)
  | cons D Ds ih =>
    simp only [List.foldr, List.mem_cons] at hC ⊢
    rcases hC with rfl | hC
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hC) (Nat.le_max_right _ _)

/-- If (ci, li) is a valid clause position, then li < positionBase N. -/
private theorem clausePos_li_lt_posBase (N : cnf) (ci li : Nat)
    (h : (ci, li) ∈ clausePositions N) : li < positionBase N := by
  obtain ⟨hci, hli⟩ := (clausePositions_mem N ci li).mp h
  exact Nat.lt_trans hli (positionBase_gt_clauseLen N (N.getD ci []) (getD_mem N ci [] hci))

------------------------------------------------------------------------
-- §9  encodePosition bounds and injectivity
------------------------------------------------------------------------

/-- An encoded position is strictly less than N.length * positionBase N. -/
private theorem encodePosition_lt (N : cnf) (ci li : Nat)
    (hci : ci < N.length) (hli : li < positionBase N) :
    encodePosition N (ci, li) < N.length * positionBase N := by
  simp only [encodePosition]
  have := positionBase_pos N
  nlinarith

/-- Decoding: div recovers ci. -/
private theorem encodePosition_div (N : cnf) (ci li : Nat)
    (hli : li < positionBase N) : encodePosition N (ci, li) / positionBase N = ci := by
  simp only [encodePosition]
  exact Nat.add_mul_div_left ci li (positionBase_pos N) |>.symm.trans
    (by omega)

/-- Decoding: mod recovers li. -/
private theorem encodePosition_mod (N : cnf) (ci li : Nat)
    (hli : li < positionBase N) : encodePosition N (ci, li) % positionBase N = li := by
  simp only [encodePosition]
  exact Nat.add_mul_mod_self_left ci li |>.symm.trans (by omega)

/-- encodePosition is injective on pairs with bounded second component. -/
private theorem encodePosition_inj (N : cnf) (ci₁ li₁ ci₂ li₂ : Nat)
    (hli₁ : li₁ < positionBase N) (hli₂ : li₂ < positionBase N)
    (heq : encodePosition N (ci₁, li₁) = encodePosition N (ci₂, li₂)) :
    ci₁ = ci₂ ∧ li₁ = li₂ := by
  simp only [encodePosition] at heq
  constructor <;> omega

------------------------------------------------------------------------
-- §10  positionCompatible: extracted properties
------------------------------------------------------------------------

/-- positionCompatible N p q = true implies p.1 ≠ q.1. -/
private theorem positionCompatible_clause_ne (N : cnf) (p q : Nat × Nat)
    (h : positionCompatible N p q = true) : p.1 ≠ q.1 := by
  simp only [positionCompatible, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

/-- positionCompatible N p q = true implies the literals are not negations. -/
private theorem positionCompatible_not_neg (N : cnf) (p q : Nat × Nat)
    (h : positionCompatible N p q = true) (l₁ l₂ : literal)
    (hl₁ : literalAt N p.1 p.2 = some l₁) (hl₂ : literalAt N q.1 q.2 = some l₂) :
    literalsAreNegations l₁ l₂ = false := by
  simp only [positionCompatible, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨_, hmatch⟩ := h
  rw [hl₁, hl₂] at hmatch
  simpa using hmatch

------------------------------------------------------------------------
-- §11  cliqueEdges membership characterisation
------------------------------------------------------------------------

private theorem cliqueEdges_mem_iff (N : cnf) (u v : Nat) :
    (u, v) ∈ cliqueEdges N ↔
    ∃ p q, p ∈ clausePositions N ∧ q ∈ clausePositions N ∧
      u = encodePosition N p ∧ v = encodePosition N q ∧
      positionCompatible N p q = true := by
  simp only [cliqueEdges, List.mem_flatMap, addCompatibleEdges,
             List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, hpPos, q, ⟨hqPos, hCompat⟩, hpair⟩
    simp [Prod.mk.injEq] at hpair
    exact ⟨p, q, hpPos, hqPos, hpair.1, hpair.2, hCompat⟩
  · rintro ⟨p, q, hpPos, hqPos, rfl, rfl, hCompat⟩
    exact ⟨p, hpPos, q, ⟨hqPos, hCompat⟩, rfl⟩

------------------------------------------------------------------------
-- §12  fgraph_wf for the reduction instance
------------------------------------------------------------------------

private theorem fgraph_wf_instance (N : cnf) :
    fgraph_wf (N.length * positionBase N, cliqueEdges N) := by
  intro e he
  rw [cliqueEdges_mem_iff] at he
  obtain ⟨p, q, hpPos, hqPos, rfl, rfl, _⟩ := he
  exact ⟨encodePosition_lt N p.1 p.2
            ((clausePositions_mem N p.1 p.2).mp hpPos).1
            (clausePos_li_lt_posBase N p.1 p.2 hpPos),
         encodePosition_lt N q.1 q.2
            ((clausePositions_mem N q.1 q.2).mp hqPos).1
            (clausePos_li_lt_posBase N q.1 q.2 hqPos)⟩

------------------------------------------------------------------------
-- §13  FlatClique of the no-instance is False
------------------------------------------------------------------------

private theorem noCliqueInstance_not_FlatClique : ¬ FlatClique noCliqueInstance := by
  simp only [FlatClique, noCliqueInstance, isfKClique, isfClique, list_ofFlatType]
  rintro ⟨l, _, ⟨⟨htype, _, _⟩, hlen⟩⟩
  -- l must have length 1, so l = [v] with v < 0
  rcases l with _ | ⟨v, _ | _⟩
  · simp at hlen
  · simp at hlen
    -- v must satisfy v < 0, impossible
    have := htype v (List.mem_cons_self v [])
    omega
  · simp at hlen

------------------------------------------------------------------------
-- §14  Forward direction: SAT N → FlatClique (instance N)
------------------------------------------------------------------------

private theorem sat_to_clique (N : cnf) (hSAT : SAT N) :
    FlatClique (kSAT_to_FlatClique_instance N) := by
  obtain ⟨a, hsat⟩ := hSAT
  -- For each clause index, find an index of a satisfied literal.
  have hExists : ∀ ci, ci < N.length →
      ∃ li, li < (N.getD ci []).length ∧
        evalLiteral a ((N.getD ci []).getD li (true, 0)) = true := fun ci hci => by
    have heval := (evalCnf_clause_iff a N).mp hsat (N.getD ci []) (getD_mem N ci [] hci)
    simp only [evalClause] at heval
    exact any_to_exists_index _ (evalLiteral a) heval
  -- Classically choose a satisfied literal index for each clause.
  let fi : ∀ ci, ci < N.length → Nat := fun ci hci => (hExists ci hci).choose
  have hfi_lt : ∀ ci (hci : ci < N.length), fi ci hci < (N.getD ci []).length :=
    fun ci hci => ((hExists ci hci).choose_spec).1
  have hfi_eval : ∀ ci (hci : ci < N.length),
      evalLiteral a ((N.getD ci []).getD (fi ci hci) (true, 0)) = true :=
    fun ci hci => ((hExists ci hci).choose_spec).2
  -- Build the clique: one vertex per clause.
  let clique : List Nat :=
    (List.finRange N.length).map (fun ⟨ci, hci⟩ => encodePosition N (ci, fi ci hci))
  refine ⟨clique, fgraph_wf_instance N, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- list_ofFlatType: all vertices are valid vertex indices.
    intro v hv
    simp only [clique, List.mem_map, List.mem_finRange] at hv
    obtain ⟨⟨ci, hci⟩, _, rfl⟩ := hv
    exact encodePosition_lt N ci (fi ci hci) hci
      (Nat.lt_trans (hfi_lt ci hci) (positionBase_gt_clauseLen N (N.getD ci [])
        (getD_mem N ci [] hci)))
  · -- Nodup: distinct Fin N.length indices give distinct encoded positions.
    apply List.Nodup.map _ (List.nodup_finRange N.length)
    intro ⟨ci₁, hci₁⟩ _ ⟨ci₂, hci₂⟩ _ henc
    have hli₁ := Nat.lt_trans (hfi_lt ci₁ hci₁)
      (positionBase_gt_clauseLen N (N.getD ci₁ []) (getD_mem N ci₁ [] hci₁))
    have hli₂ := Nat.lt_trans (hfi_lt ci₂ hci₂)
      (positionBase_gt_clauseLen N (N.getD ci₂ []) (getD_mem N ci₂ [] hci₂))
    have := (encodePosition_inj N ci₁ _ ci₂ _ hli₁ hli₂ henc).1
    simp [Fin.ext_iff, this]
  · -- All distinct pairs are connected in cliqueEdges N.
    intro v₁ v₂ hv₁ hv₂ hne
    simp only [clique, List.mem_map, List.mem_finRange] at hv₁ hv₂
    obtain ⟨⟨ci₁, hci₁⟩, _, rfl⟩ := hv₁
    obtain ⟨⟨ci₂, hci₂⟩, _, rfl⟩ := hv₂
    -- Distinct vertices come from distinct clause indices.
    have hciNe : ci₁ ≠ ci₂ := by
      intro heq
      apply hne
      simp [heq]
    -- Retrieve the literals at the two positions.
    let li₁ := fi ci₁ hci₁
    let li₂ := fi ci₂ hci₂
    have hli₁_lt := Nat.lt_trans (hfi_lt ci₁ hci₁)
      (positionBase_gt_clauseLen N (N.getD ci₁ []) (getD_mem N ci₁ [] hci₁))
    have hli₂_lt := Nat.lt_trans (hfi_lt ci₂ hci₂)
      (positionBase_gt_clauseLen N (N.getD ci₂ []) (getD_mem N ci₂ [] hci₂))
    -- Build the edge via cliqueEdges_mem_iff.
    rw [cliqueEdges_mem_iff]
    refine ⟨(ci₁, li₁), (ci₂, li₂),
      (clausePositions_mem N ci₁ li₁).mpr ⟨hci₁, hfi_lt ci₁ hci₁⟩,
      (clausePositions_mem N ci₂ li₂).mpr ⟨hci₂, hfi_lt ci₂ hci₂⟩,
      rfl, rfl, ?_⟩
    -- positionCompatible: different clauses and literals not negations.
    simp only [positionCompatible, bne_iff_ne, Bool.and_eq_true]
    refine ⟨hciNe, ?_⟩
    -- Show that the literals at (ci₁, li₁) and (ci₂, li₂) are not negations.
    obtain ⟨l₁, hl₁⟩ := clausePositions_literalAt_some N ci₁ li₁
      ((clausePositions_mem N ci₁ li₁).mpr ⟨hci₁, hfi_lt ci₁ hci₁⟩)
    obtain ⟨l₂, hl₂⟩ := clausePositions_literalAt_some N ci₂ li₂
      ((clausePositions_mem N ci₂ li₂).mpr ⟨hci₂, hfi_lt ci₂ hci₂⟩)
    rw [hl₁, hl₂]
    simp only [Bool.not_eq_true']
    -- Prove not negations by contradiction: if they were, one would be true and the other false.
    intro hNeg
    simp only [literalsAreNegations, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hNeg
    obtain ⟨hVar, hPol⟩ := hNeg
    -- Recover the literal values from literalAt.
    have hget₁ : (N.getD ci₁ []).getD li₁ (true, 0) = l₁ := by
      rw [literalAt_eq, get?_eq_some_getD N ci₁ [] hci₁,
          get?_eq_some_getD (N.getD ci₁ []) li₁ (true, 0) (hfi_lt ci₁ hci₁)] at hl₁
      simpa using hl₁
    have hget₂ : (N.getD ci₂ []).getD li₂ (true, 0) = l₂ := by
      rw [literalAt_eq, get?_eq_some_getD N ci₂ [] hci₂,
          get?_eq_some_getD (N.getD ci₂ []) li₂ (true, 0) (hfi_lt ci₂ hci₂)] at hl₂
      simpa using hl₂
    -- Both literals are satisfied by a.
    have heval₁ : evalLiteral a l₁ = true := hget₁ ▸ hfi_eval ci₁ hci₁
    have heval₂ : evalLiteral a l₂ = true := hget₂ ▸ hfi_eval ci₂ hci₂
    -- l₁ and l₂ have the same variable but opposite polarities.
    rcases l₁ with ⟨pol₁, var₁⟩
    rcases l₂ with ⟨pol₂, var₂⟩
    simp only [literalVar, literalPolarity] at hVar hPol
    subst hVar  -- var₁ = var₂, call it var₂
    simp only [evalLiteral, decide_eq_true_eq] at heval₁ heval₂
    -- heval₁ : evalVar a var₂ = pol₁
    -- heval₂ : evalVar a var₂ = pol₂
    -- pol₁ ≠ pol₂ but both equal evalVar a var₂.  Contradiction.
    exact hPol (heval₁.symm.trans heval₂)
  · -- Length equals N.length.
    simp [clique, List.length_map, List.length_finRange]

------------------------------------------------------------------------
-- §15  Backward direction: FlatClique (instance N) → SAT N
------------------------------------------------------------------------

/-- A nonempty clause is always satisfiable. -/
private theorem nonempty_clause_sat (C : clause) (hC : 0 < C.length) : SAT [C] := by
  -- Take the first literal and set its variable appropriately.
  let l := C.get ⟨0, hC⟩
  let a : assgn := if l.1 then [l.2] else []
  refine ⟨a, ?_⟩
  simp only [satisfiesCnf, evalCnf, evalClause, List.all_cons, List.all_nil]
  simp only [List.any_eq_true]
  refine ⟨l, List.get_mem C 0 hC, ?_⟩
  simp only [evalLiteral, a]
  rcases l with ⟨pol, var⟩
  simp only
  rcases pol with _ | _
  · simp [evalVar]
  · simp [evalVar]

/-- From a clique in the instance graph, extract a satisfying assignment for N
    (for the case N.length ≥ 2). -/
private theorem clique_to_sat_of_length_ge_two (N : cnf) (k : Nat) (hk : 0 < k)
    (hkCNF : kCNF k N) (hN2 : 2 ≤ N.length)
    (l : List fvertex) (hwf : fgraph_wf (kSAT_to_FlatClique_instance N).1)
    (hclique : isfClique (kSAT_to_FlatClique_instance N).1 l)
    (hlen : l.length = N.length) : SAT N := by
  obtain ⟨htype, hnodup, hadj⟩ := hclique
  -- Every vertex in the clique is in some edge (since |l| ≥ 2 and all pairs adjacent).
  -- Extract the position for each vertex.
  have hDecode : ∀ v ∈ l, ∃ p ∈ clausePositions N, v = encodePosition N p := by
    intro v hv
    -- Since l has ≥ 2 elements and Nodup, pick another w ≠ v.
    have hother : ∃ w ∈ l, w ≠ v := by
      rw [← hlen] at hN2
      -- l.length ≥ 2 and l.Nodup, so there are at least 2 distinct elements.
      cases l with
      | nil => simp at hN2
      | cons a as =>
        cases as with
        | nil => simp at hN2
        | cons b bs =>
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · -- v = a; take w = b
            have hne : b ≠ a := by
              have := hnodup
              simp [List.Nodup, List.not_mem_cons] at this
              exact this.1.1
            exact ⟨b, by simp, hne.symm⟩
          · -- v ∈ b :: bs; take w = a
            exact ⟨a, by simp, by
              intro heq
              subst heq
              have := hnodup
              simp [List.Nodup] at this
              exact this.1.1 (by
                rcases hv with rfl | hv
                · exact List.mem_cons_self _ _
                · exact List.mem_cons_of_mem _ hv)⟩
    obtain ⟨w, hw, hne⟩ := hother
    -- (v, w) is an edge in the clique.
    have hedge : (v, w) ∈ (kSAT_to_FlatClique_instance N).1.2 := hadj v w hv hw hne
    simp only [kSAT_to_FlatClique_instance] at hedge
    rw [cliqueEdges_mem_iff] at hedge
    obtain ⟨p, _, hp, _, rfl, _, _⟩ := hedge
    exact ⟨p, hp, rfl⟩
  -- All clause indices in the clique are distinct.
  have hciDistinct : ∀ v w, v ∈ l → w ∈ l → v ≠ w →
      v / positionBase N ≠ w / positionBase N := by
    intro v w hv hw hne
    obtain ⟨p, hp, hveq⟩ := hDecode v hv
    obtain ⟨q, hq, hweq⟩ := hDecode w hw
    have hedge : (v, w) ∈ (kSAT_to_FlatClique_instance N).1.2 := hadj v w hv hw hne
    simp only [kSAT_to_FlatClique_instance] at hedge
    rw [cliqueEdges_mem_iff] at hedge
    obtain ⟨p', q', _, _, hvp', hwq', hcompat⟩ := hedge
    have hpbase := clausePos_li_lt_posBase N p.1 p.2 hp
    have hqbase := clausePos_li_lt_posBase N q.1 q.2 hq
    -- v = enc(p) = enc(p') so p = p' (by injectivity and both have second component < posBase)
    rw [hveq] at hvp'
    have hpp' : p = p' := by
      obtain ⟨hci, hli⟩ := encodePosition_inj N p.1 p.2 p'.1 p'.2
        hpbase (clausePos_li_lt_posBase N p'.1 p'.2 ‹_›) hvp'
      exact Prod.ext hci hli
    subst hpp'
    rw [hveq, encodePosition_div N p.1 p.2 hpbase]
    rw [hweq]
    -- Similarly decode w
    obtain ⟨hqbase'⟩ := clausePos_li_lt_posBase N q'.1 q'.2 ‹_›
    rw [hwq', encodePosition_div N q'.1 q'.2 (clausePos_li_lt_posBase N q'.1 q'.2 ‹_›)]
    exact positionCompatible_clause_ne N p q' hcompat
  -- The map v ↦ v / positionBase N is injective on l, all values < N.length.
  have hciRange : ∀ v ∈ l, v / positionBase N < N.length := by
    intro v hv
    obtain ⟨p, hp, hveq⟩ := hDecode v hv
    rw [hveq, encodePosition_div N p.1 p.2 (clausePos_li_lt_posBase N p.1 p.2 hp)]
    exact (clausePositions_mem N p.1 p.2).mp hp |>.1
  -- The N.length distinct clause indices {v/posBase | v ∈ l} ⊆ {0,..,N.length-1}
  -- and l.length = N.length, so every clause index is covered.
  have hciSurj : ∀ ci < N.length, ∃ v ∈ l, v / positionBase N = ci := by
    intro ci hci
    -- l.map (· / positionBase N) is a Nodup list of length N.length in {0,..,N.length-1}
    -- hence it equals {0,..,N.length-1}.
    let lci := l.map (· / positionBase N)
    have hlci_nodup : lci.Nodup := by
      apply List.Nodup.map hnodup
      intro a ha b hb hab
      by_contra hne
      exact hciDistinct a b ha hb hne hab
    have hlci_len : lci.length = N.length := by
      simp [lci, List.length_map, hlen]
    have hlci_range : ∀ x ∈ lci, x < N.length := by
      intro x hx
      simp only [lci, List.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      exact hciRange v hv
    -- A Nodup list of length N.length with all values < N.length covers everything.
    have : ci ∈ lci := by
      by_contra h
      have hle : lci.length ≤ (List.range N.length).length - 1 := by
        rw [List.length_range]
        have : lci ⊆ (List.range N.length).erase ci := by
          intro x hx
          rw [List.mem_erase_of_ne]
          · rw [List.mem_range]; exact hlci_range x hx
          · intro heq
            exact h (heq ▸ hx)
        have hnodup_range_erase : ((List.range N.length).erase ci).Nodup :=
          (List.nodup_range N.length).erase ci
        have := List.Nodup.length_le_of_nodup_sublist hlci_nodup
          (List.nodup_sublist hnodup_range_erase this)
        simp [List.length_erase_of_mem (List.mem_range.mpr hci)] at this
        omega
      simp [List.length_range] at hle
      omega
    simp only [lci, List.mem_map] at this
    exact this
  -- Build the satisfying assignment: for each v ∈ l with literal (true, var), add var.
  let a : assgn := l.filterMap fun v =>
    match literalAt N (v / positionBase N) (v % positionBase N) with
    | some (true, var) => some var
    | _ => none
  -- Verify a satisfies N.
  refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
  intro C hC
  -- Find the clause index ci for C.
  have hC_idx : ∃ ci < N.length, N.getD ci [] = C := by
    rw [List.mem_iff_get] at hC
    obtain ⟨⟨ci, hci⟩, hget⟩ := hC
    exact ⟨ci, hci, by rwa [getD_eq_get _ ci [] hci]⟩
  obtain ⟨ci, hci, rfl⟩ := hC_idx
  -- Get the vertex v in l covering clause ci.
  obtain ⟨v, hv, hciV⟩ := hciSurj ci hci
  -- Decode v to its position.
  obtain ⟨p, hp, hveq⟩ := hDecode v hv
  have hpbase := clausePos_li_lt_posBase N p.1 p.2 hp
  have hpci := (clausePositions_mem N p.1 p.2).mp hp
  -- p.1 = ci (from hciV and the decode)
  have hpciEq : p.1 = ci := by
    rw [hveq, encodePosition_div N p.1 p.2 hpbase] at hciV
    exact hciV
  -- Get the literal at position (ci, p.2).
  obtain ⟨lit, hlit⟩ := clausePositions_literalAt_some N p.1 p.2 hp
  rw [hpciEq] at hlit
  -- The literal is in the clause.
  rw [evalClause_literal_iff]
  refine ⟨lit, ?_, ?_⟩
  · -- lit ∈ N.getD ci []
    rw [literalAt_eq, get?_eq_some_getD N ci [] hci,
        get?_eq_some_getD (N.getD ci []) p.2 (true, 0)
          (hpciEq ▸ hpci.2)] at hlit
    simp at hlit
    exact getD_mem (N.getD ci []) p.2 (true, 0) (hpciEq ▸ hpci.2) |> hlit ▸ id
  · -- evalLiteral a lit = true
    rcases lit with ⟨pol, var⟩
    simp only [evalLiteral, decide_eq_true_eq]
    rcases pol with _ | _
    · -- pol = false: need evalVar a var = false
      simp only [evalVar, Bool.decide_eq_false_iff_ne, ne_eq]
      intro hmem
      -- var ∈ a means some v' ∈ l has literal (true, var)
      simp only [a, List.mem_filterMap] at hmem
      obtain ⟨v', hv', hmatch⟩ := hmem
      -- v' decodes to literal (true, var)
      obtain ⟨p', hp', hv'eq⟩ := hDecode v' hv'
      have hp'base := clausePos_li_lt_posBase N p'.1 p'.2 hp'
      -- The literal at v' is (true, var)
      have hlitV' : literalAt N (v' / positionBase N) (v' % positionBase N) = some (true, var) := by
        split at hmatch
        · rename_i b w h
          rcases b with _ | _
          · exact h ▸ (by injection hmatch with h'; rw [← h']; exact h)
          · simp at hmatch
        · simp at hmatch
      -- v ≠ v' (since they have the same ci = v/posBase = v'/posBase via var check... need careful reasoning)
      -- We have: lit at (ci, p.2) = (false, var) and lit at (p'.1, p'.2) = (true, var)
      -- These are negations, so positionCompatible = false
      -- But if ci = p'.1 (same clause), then since l.Nodup and both have ci, v = v' (same clause index in distinct list)
      -- Wait, actually v and v' might have the same clause index, but they're distinct elements.
      -- Since l.Nodup and v/posBase = v'/posBase would mean v = v' (by hciDistinct... contradiction with v ≠ v').
      -- OR v ≠ v', so (v, v') is an edge, giving positionCompatible (ci, p.2) (p'.1, p'.2) = true.
      -- But the literals (false, var) and (true, var) ARE negations. Contradiction.
      have hv'ne : v' ≠ v := by
        intro heq; subst heq
        -- v has literal (false, var) but we claimed (true, var) for the match
        rw [hveq, encodePosition_div N p.1 p.2 hpbase,
            encodePosition_mod N p.1 p.2 hpbase] at hlitV'
        rw [hlit] at hlitV'
        injection hlitV'
      have hedge : (v, v') ∈ (kSAT_to_FlatClique_instance N).1.2 :=
        hadj v v' hv hv' (Ne.symm hv'ne)
      simp only [kSAT_to_FlatClique_instance] at hedge
      rw [cliqueEdges_mem_iff] at hedge
      obtain ⟨px, py, _, _, hvpx, hv'py, hcompat⟩ := hedge
      -- Decode: px is the position of v, py is the position of v'
      rw [hveq, encodePosition_div N p.1 p.2 hpbase,
          encodePosition_mod N p.1 p.2 hpbase] at hvpx
      obtain ⟨hci_eq, hli_eq⟩ : px.1 = p.1 ∧ px.2 = p.2 := by
        have := encodePosition_inj N p.1 p.2 px.1 px.2 hpbase
          (clausePos_li_lt_posBase N px.1 px.2 ‹_›) hvpx
        exact ⟨this.1, this.2⟩
      -- The literal at px = (p.1, p.2) = (false, var)
      have hlitpx : literalAt N px.1 px.2 = some (false, var) := by
        rw [hci_eq, hli_eq]; exact hlit
      -- Decode v': py is the position of v'
      rw [hv'eq, encodePosition_div N p'.1 p'.2 hp'base,
          encodePosition_mod N p'.1 p'.2 hp'base] at hv'py
      obtain ⟨hci'_eq, hli'_eq⟩ : py.1 = p'.1 ∧ py.2 = p'.2 := by
        have := encodePosition_inj N p'.1 p'.2 py.1 py.2 hp'base
          (clausePos_li_lt_posBase N py.1 py.2 ‹_›) hv'py
        exact ⟨this.1, this.2⟩
      have hlitpy : literalAt N py.1 py.2 = some (true, var) := by
        rw [hci'_eq, hli'_eq]
        rw [hveq, encodePosition_div N p.1 p.2 hpbase,
            encodePosition_mod N p.1 p.2 hpbase] at hlitV'
        rw [hv'eq, encodePosition_div N p'.1 p'.2 hp'base,
            encodePosition_mod N p'.1 p'.2 hp'base] at hlitV'
        exact hlitV'
      -- (false, var) and (true, var) are negations, but positionCompatible says they're not.
      have hnotNeg := positionCompatible_not_neg N px py hcompat (false, var) (true, var)
        hlitpx hlitpy
      simp [literalsAreNegations, literalVar, literalPolarity] at hnotNeg
    · -- pol = true: need evalVar a var = true, i.e., var ∈ a
      simp only [evalVar, decide_eq_true_eq]
      -- Show var ∈ a by showing v is in the filterMap with literal (true, var)
      simp only [a, List.mem_filterMap]
      refine ⟨v, hv, ?_⟩
      rw [hveq, encodePosition_div N p.1 p.2 hpbase,
          encodePosition_mod N p.1 p.2 hpbase, hlit]

------------------------------------------------------------------------
-- §16  Correctness of the guarded reduction
------------------------------------------------------------------------

private theorem kSAT_to_FlatClique_f_correct (k : Nat) (N : cnf) :
    kSAT k N ↔ FlatClique (kSAT_to_FlatClique_f k N) := by
  simp only [kSAT_to_FlatClique_f]
  by_cases hcond : 0 < k ∧ kCNF k N
  · simp only [hcond, ↓reduceIte]
    obtain ⟨hk, hkCNF⟩ := hcond
    constructor
    · rintro ⟨_, _, hSAT⟩
      exact sat_to_clique N hSAT
    · intro hClique
      refine ⟨hk, hkCNF, ?_⟩
      -- Dispatch on N.length
      rcases Nat.lt_or_ge N.length 2 with hlt2 | hge2
      · -- N.length = 0 or 1
        interval_cases (N.length)
        · -- N = [], SAT [] trivially
          exact ⟨[], by simp [satisfiesCnf, evalCnf]⟩
        · -- N.length = 1: single-clause CNF, nonempty clause is satisfiable
          have hClen : ∀ C ∈ N, C.length = k := (kCNF_clause_length k N).mp hkCNF
          rcases N with _ | ⟨C, ⟨⟩⟩
          -- N = [C]
          have hCpos : 0 < C.length := by
            have := hClen C (List.mem_cons_self C [])
            omega
          obtain ⟨a, ha⟩ := nonempty_clause_sat C hCpos
          simp only [SAT, satisfiesCnf, evalCnf] at ha ⊢
          exact ⟨a, by simpa [evalCnf] using ha⟩
      · -- N.length ≥ 2: use the clique structure
        obtain ⟨l, _, hclique, hlen⟩ := hClique
        exact clique_to_sat_of_length_ge_two N k hk hkCNF hge2 l
          (fgraph_wf_instance N) hclique hlen
  · simp only [hcond, ↓reduceIte]
    constructor
    · rintro ⟨hk, hkCNF, _⟩
      exact absurd ⟨hk, hkCNF⟩ hcond
    · intro h
      exact absurd h noCliqueInstance_not_FlatClique

------------------------------------------------------------------------
-- §17  Size bound helpers
------------------------------------------------------------------------

/-- encodable.size of a List α is at least the list length. -/
private theorem encodable_size_list_ge_length {α : Type} [encodable α] (l : List α) :
    l.length ≤ encodable.size l := by
  induction l with
  | nil => simp [encodable.size]
  | cons x xs ih =>
    rw [encodable_size_list_cons]
    simp only [List.length_cons]
    omega

/-- N.length ≤ encodable.size N. -/
private theorem cnf_length_le_size (N : cnf) : N.length ≤ encodable.size N :=
  encodable_size_list_ge_length N

/-- positionBase N ≤ encodable.size N + 1. -/
private theorem positionBase_le_size_add_one (N : cnf) :
    positionBase N ≤ encodable.size N + 1 := by
  simp only [positionBase]
  suffices h : N.foldr (fun C acc => Nat.max C.length acc) 0 ≤ encodable.size N by omega
  induction N with
  | nil => simp [encodable.size]
  | cons C Cs ih =>
    simp only [List.foldr, encodable_size_list_cons]
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_trans (encodable_size_list_ge_length C) (by omega)
    · exact Nat.le_trans ih (by omega)

/-- clausePositions N has length ≤ encodable.size N. -/
private theorem clausePositions_length_le_size (N : cnf) :
    (clausePositions N).length ≤ encodable.size N := by
  simp only [clausePositions]
  induction N with
  | nil => simp [clausePositionsAux, encodable.size]
  | cons C Cs ih =>
    simp only [clausePositionsAux, List.length_append, List.length_map, List.length_range,
               encodable_size_list_cons]
    calc C.length + (clausePositionsAux Cs 1).length
        ≤ encodable.size C + ih := by
          apply Nat.add_le_add_right
          exact encodable_size_list_ge_length C
      _ ≤ encodable.size C + encodable.size Cs := Nat.add_le_add_left ih _
      _ ≤ encodable.size C + 1 + encodable.size Cs := by omega

/-- encodable.size (l : List (Nat × Nat)) ≤ l.length * (2 * B + 2) when all
    pairs have components < B. -/
private theorem encodable_size_fedge_list_bounded (B : Nat) (edges : List fedge)
    (hbound : ∀ e ∈ edges, e.1 < B ∧ e.2 < B) :
    encodable.size edges ≤ edges.length * (2 * B + 2) := by
  induction edges with
  | nil => simp [encodable.size]
  | cons e es ih =>
    rw [encodable_size_list_cons]
    have he := hbound e (List.mem_cons_self e es)
    have ihb : encodable.size es ≤ es.length * (2 * B + 2) := by
      apply ih; intro e' he'; exact hbound e' (List.mem_cons_of_mem _ he')
    simp only [List.length_cons]
    have hsize_e : encodable.size e = e.1 + e.2 + 1 := rfl
    rw [hsize_e]
    nlinarith [he.1, he.2]

/-- cliqueEdges N has length ≤ (clausePositions N).length ^ 2. -/
private theorem cliqueEdges_length_le (N : cnf) :
    (cliqueEdges N).length ≤ (clausePositions N).length ^ 2 := by
  simp only [cliqueEdges]
  calc (clausePositions N).flatMap (addCompatibleEdges N (clausePositions N)) |>.length
      ≤ (clausePositions N).length * (clausePositions N).length := by
        apply List.length_flatMap_le
        intro p _
        simp only [addCompatibleEdges, List.length_map, List.length_filter]
        exact Nat.le_refl _
      _ = _ := by ring

/-- All edges in cliqueEdges N have endpoints < N.length * positionBase N. -/
private theorem cliqueEdges_endpoints_lt (N : cnf) (e : fedge)
    (he : e ∈ cliqueEdges N) : e.1 < N.length * positionBase N ∧ e.2 < N.length * positionBase N := by
  rw [cliqueEdges_mem_iff] at he
  obtain ⟨p, q, hp, hq, rfl, rfl, _⟩ := he
  exact ⟨encodePosition_lt N p.1 p.2 (clausePositions_mem N p.1 p.2 |>.mp hp).1
            (clausePos_li_lt_posBase N p.1 p.2 hp),
         encodePosition_lt N q.1 q.2 (clausePositions_mem N q.1 q.2 |>.mp hq).1
            (clausePos_li_lt_posBase N q.1 q.2 hq)⟩

/-- encodable.size (cliqueEdges N) ≤ 6 * (encodable.size N)^4 + 6. -/
private theorem encodable_size_cliqueEdges_le (N : cnf) :
    encodable.size (cliqueEdges N) ≤
    6 * (encodable.size N) ^ 4 + 6 := by
  set S := encodable.size N
  set B := N.length * positionBase N
  have hNlenS : N.length ≤ S := cnf_length_le_size N
  have hpbaseS : positionBase N ≤ S + 1 := positionBase_le_size_add_one N
  have hBS : B ≤ S * (S + 1) := Nat.mul_le_mul hNlenS hpbaseS
  have hcpS : (clausePositions N).length ≤ S := clausePositions_length_le_size N
  -- Bound the number of edges
  have hNumEdges : (cliqueEdges N).length ≤ S ^ 2 :=
    Nat.le_trans (cliqueEdges_length_le N) (by
      apply Nat.pow_le_pow_left
      exact hcpS)
  -- Bound each edge's size
  have hEdgeBound : ∀ e ∈ cliqueEdges N,
      e.1 < N.length * positionBase N ∧ e.2 < N.length * positionBase N :=
    cliqueEdges_endpoints_lt N
  -- Apply the list size bound
  have hSizeBound := encodable_size_fedge_list_bounded B
    (cliqueEdges N) (fun e he => hEdgeBound e he)
  have hBound : 2 * B + 2 ≤ 2 * S ^ 2 + 4 := by nlinarith [Nat.zero_le S]
  calc encodable.size (cliqueEdges N)
      ≤ (cliqueEdges N).length * (2 * B + 2) := hSizeBound
    _ ≤ S ^ 2 * (2 * S ^ 2 + 4) := Nat.mul_le_mul hNumEdges hBound
    _ ≤ 6 * S ^ 4 + 6 := by nlinarith [Nat.zero_le S, Nat.zero_le (S^2)]

/-- Size bound for the reduction instance. -/
private theorem kSAT_to_FlatClique_f_size_bound (k : Nat) (N : cnf) :
    encodable.size (kSAT_to_FlatClique_f k N) ≤ 10 * (encodable.size N) ^ 4 + 10 := by
  simp only [kSAT_to_FlatClique_f]
  by_cases hcond : 0 < k ∧ kCNF k N
  · simp only [hcond, ↓reduceIte, kSAT_to_FlatClique_instance]
    set S := encodable.size N
    have hNlenS : N.length ≤ S := cnf_length_le_size N
    have hpbaseS : positionBase N ≤ S + 1 := positionBase_le_size_add_one N
    have hBS : N.length * positionBase N ≤ S * (S + 1) := Nat.mul_le_mul hNlenS hpbaseS
    have hCE : encodable.size (cliqueEdges N) ≤ 6 * S ^ 4 + 6 :=
      encodable_size_cliqueEdges_le N
    -- Compute the total size
    have hTotal : encodable.size ((N.length * positionBase N, cliqueEdges N), N.length) =
        N.length * positionBase N + encodable.size (cliqueEdges N) + N.length + 2 := by
      simp only [encodable.size]; ring
    rw [hTotal]
    nlinarith [Nat.zero_le S, Nat.zero_le (S^2), Nat.zero_le (S^3)]
  · simp only [hcond, ↓reduceIte, noCliqueInstance]
    simp only [encodable.size]
    nlinarith [Nat.zero_le (encodable.size N), Nat.zero_le ((encodable.size N)^4)]

------------------------------------------------------------------------
-- §18  Main polynomial-time reduction theorem
------------------------------------------------------------------------

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique :=
  ⟨⟨kSAT_to_FlatClique_f k,
    ⟨⟨fun n => 10 * n ^ 4 + 10,
      -- bound_poly: 10 * n^4 + 10 is a polynomial
      by
        apply inOPoly_add
        · exact ⟨4, ⟨10, 1, by intro n hn; nlinarith [Nat.one_le_pow 4 n (by omega)]⟩⟩
        · exact inOPoly_const 10,
      -- bound_mono: 10 * n^4 + 10 is monotone
      by
        intro a b hab
        nlinarith [Nat.pow_le_pow_left hab 4],
      -- bound_valid: size of reduction output ≤ bound of input size
      kSAT_to_FlatClique_f_size_bound k⟩⟩,
    fun {N} => kSAT_to_FlatClique_f_correct k N⟩⟩
