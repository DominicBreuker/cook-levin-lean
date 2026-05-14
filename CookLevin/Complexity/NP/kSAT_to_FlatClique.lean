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
    encode clause-literal positions; the required k-clique size is N.length. -/
def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  ((N.length * positionBase N, cliqueEdges N), N.length)

/-- Trivial no-instance: vertex bound 0 makes any 1-clique impossible. -/
private def noCliqueInstance : fgraph × Nat := ((0, []), 1)

/-- Guarded reduction: applies the Karp construction on valid k-CNF inputs,
    maps everything else to the no-instance. -/
private noncomputable def kSAT_to_FlatClique_f (k : Nat) (N : cnf) : fgraph × Nat :=
  if 0 < k ∧ kCNF k N then kSAT_to_FlatClique_instance N else noCliqueInstance

------------------------------------------------------------------------
-- §5  nthClause / nthLiteral
------------------------------------------------------------------------

private theorem nthClause_none_of_ge {N : cnf} {i : Nat} (h : N.length ≤ i) :
    nthClause N i = none := by
  induction N generalizing i with
  | nil => rfl
  | cons C Cs ih =>
    cases i with
    | zero => simp at h
    | succ i => simpa [nthClause] using ih (by simpa using h)

private theorem nthClause_eq_getD {N : cnf} {i : Nat} (h : i < N.length) :
    nthClause N i = some (N.getD i []) := by
  induction N generalizing i with
  | nil => simp at h
  | cons C Cs ih =>
    cases i with
    | zero => simp [nthClause, List.getD]
    | succ i =>
      simp only [nthClause]
      rw [ih (by simpa using h)]
      simp [List.getD]

private theorem nthLiteral_none_of_ge {C : clause} {i : Nat} (h : C.length ≤ i) :
    nthLiteral C i = none := by
  induction C generalizing i with
  | nil => rfl
  | cons l ls ih =>
    cases i with
    | zero => simp at h
    | succ i => simpa [nthLiteral] using ih (by simpa using h)

private theorem nthLiteral_eq_getD {C : clause} {i : Nat} (h : i < C.length) :
    nthLiteral C i = some (C.getD i (true, 0)) := by
  induction C generalizing i with
  | nil => simp at h
  | cons l ls ih =>
    cases i with
    | zero => simp [nthLiteral, List.getD]
    | succ i =>
      simp only [nthLiteral]
      rw [ih (by simpa using h)]
      simp [List.getD]

/-- When the bounds hold, literalAt returns some literal. -/
private theorem literalAt_eq_some (N : cnf) (ci li : Nat)
    (hci : ci < N.length) (hli : li < (N.getD ci []).length) :
    literalAt N ci li = some ((N.getD ci []).getD li (true, 0)) := by
  show (do let C ← nthClause N ci; nthLiteral C li) = _
  rw [nthClause_eq_getD hci]
  exact nthLiteral_eq_getD hli

------------------------------------------------------------------------
-- §6  getD utility lemmas
------------------------------------------------------------------------

/-- When n < l.length, l.getD n d is a member of l. -/
private theorem getD_mem {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => exact List.mem_cons_self
    | succ n =>
      have hn : n < xs.length := Nat.lt_of_succ_lt_succ h
      exact List.mem_cons_of_mem x (ih n hn)

/-- When n < l.length, l.getD n d = l.get ⟨n, h⟩. -/
private theorem getD_eq_get {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d = l.get ⟨n, h⟩ := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (Nat.lt_of_succ_lt_succ h)

/-- For any nonempty clause, there is a satisfied literal index when the
    clause evaluates to true. -/
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
      exact ⟨i + 1, Nat.succ_lt_succ hi, hpi⟩

------------------------------------------------------------------------
-- §7  clausePositions membership
------------------------------------------------------------------------

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
          simp [Prod.mk.injEq] at hpair; exact ⟨hpair.1.symm, hpair.2.symm⟩
        subst hci hli
        exact ⟨le_refl _, by simp, by simp [List.getD]; exact hli'⟩
      · obtain ⟨hle, hlen, hliD⟩ := (ih (base + 1) ci).mp hmem
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
        rw [ih (base + 1) ci]
        refine ⟨hlt, ?_, ?_⟩
        · have : ci - base = ci - (base + 1) + 1 := by omega
          rw [this] at hlen; simpa using hlen
        · have : ci - base = ci - (base + 1) + 1 := by omega
          rw [this] at hliD; simpa [List.getD] using hliD

private theorem clausePositions_mem (N : cnf) (ci li : Nat) :
    (ci, li) ∈ clausePositions N ↔
    ci < N.length ∧ li < (N.getD ci []).length := by
  simp only [clausePositions, clausePositionsAux_mem N 0 ci li, Nat.sub_zero]
  omega

private theorem clausePositions_literalAt_some (N : cnf) (ci li : Nat)
    (h : (ci, li) ∈ clausePositions N) : ∃ l, literalAt N ci li = some l := by
  obtain ⟨hci, hli⟩ := (clausePositions_mem N ci li).mp h
  exact ⟨_, literalAt_eq_some N ci li hci hli⟩

------------------------------------------------------------------------
-- §8  positionBase bounds
------------------------------------------------------------------------

private theorem positionBase_pos (N : cnf) : 0 < positionBase N :=
  Nat.succ_pos _

private theorem positionBase_gt_clauseLen (N : cnf) (C : clause) (hC : C ∈ N) :
    C.length < positionBase N := by
  simp only [positionBase]
  suffices h : C.length ≤ N.foldr (fun D acc => Nat.max D.length acc) 0 by omega
  induction N with
  | nil => exact absurd hC List.not_mem_nil
  | cons D Ds ih =>
    simp only [List.foldr, List.mem_cons] at hC ⊢
    rcases hC with rfl | hC
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hC) (Nat.le_max_right _ _)

private theorem clausePos_li_lt_posBase (N : cnf) (ci li : Nat)
    (h : (ci, li) ∈ clausePositions N) : li < positionBase N :=
  Nat.lt_trans ((clausePositions_mem N ci li).mp h).2
    (positionBase_gt_clauseLen N (N.getD ci [])
      (getD_mem N ci [] ((clausePositions_mem N ci li).mp h).1))

------------------------------------------------------------------------
-- §9  encodePosition bounds and injectivity
------------------------------------------------------------------------

private theorem encodePosition_lt (N : cnf) (ci li : Nat)
    (hci : ci < N.length) (hli : li < positionBase N) :
    encodePosition N (ci, li) < N.length * positionBase N := by
  simp only [encodePosition]
  have := positionBase_pos N
  nlinarith

private theorem encodePosition_div (N : cnf) (ci li : Nat)
    (hli : li < positionBase N) : encodePosition N (ci, li) / positionBase N = ci := by
  simp only [encodePosition]
  exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _)
    (by nlinarith [positionBase_pos N])

private theorem encodePosition_mod (N : cnf) (ci li : Nat)
    (hli : li < positionBase N) : encodePosition N (ci, li) % positionBase N = li := by
  simp only [encodePosition]
  rw [Nat.add_mod,
      show ci * positionBase N % positionBase N = 0 from
        by rw [Nat.mul_comm]; exact Nat.mul_mod_right (positionBase N) ci,
      Nat.zero_add,
      Nat.mod_eq_of_lt (Nat.mod_lt li (positionBase_pos N)),
      Nat.mod_eq_of_lt hli]

private theorem encodePosition_inj (N : cnf) (ci₁ li₁ ci₂ li₂ : Nat)
    (hli₁ : li₁ < positionBase N) (hli₂ : li₂ < positionBase N)
    (heq : encodePosition N (ci₁, li₁) = encodePosition N (ci₂, li₂)) :
    ci₁ = ci₂ ∧ li₁ = li₂ :=
  ⟨(encodePosition_div N ci₁ li₁ hli₁).symm.trans
      (heq ▸ encodePosition_div N ci₂ li₂ hli₂),
   (encodePosition_mod N ci₁ li₁ hli₁).symm.trans
      (heq ▸ encodePosition_mod N ci₂ li₂ hli₂)⟩

------------------------------------------------------------------------
-- §10  positionCompatible: extracted properties
------------------------------------------------------------------------

private theorem positionCompatible_clause_ne (N : cnf) (p q : Nat × Nat)
    (h : positionCompatible N p q = true) : p.1 ≠ q.1 := by
  simp only [positionCompatible, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

private theorem positionCompatible_not_neg (N : cnf) (p q : Nat × Nat)
    (h : positionCompatible N p q = true) (l₁ l₂ : literal)
    (hl₁ : literalAt N p.1 p.2 = some l₁) (hl₂ : literalAt N q.1 q.2 = some l₂) :
    literalsAreNegations l₁ l₂ = false := by
  simp only [positionCompatible, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨_, hmatch⟩ := h
  rw [hl₁, hl₂] at hmatch
  simpa using hmatch

------------------------------------------------------------------------
-- §11  cliqueEdges membership
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
    have hp1 : u = encodePosition N p := (Prod.mk.inj hpair).1.symm
    have hp2 : v = encodePosition N q := (Prod.mk.inj hpair).2.symm
    exact ⟨p, q, hpPos, hqPos, hp1, hp2, hCompat⟩
  · rintro ⟨p, q, hpPos, hqPos, rfl, rfl, hCompat⟩
    exact ⟨p, hpPos, q, ⟨hqPos, hCompat⟩, rfl⟩

------------------------------------------------------------------------
-- §12  fgraph_wf for the reduction instance
------------------------------------------------------------------------

private theorem cliqueEdges_endpoints_lt (N : cnf) (e : fedge)
    (he : e ∈ cliqueEdges N) :
    e.1 < N.length * positionBase N ∧ e.2 < N.length * positionBase N := by
  rw [cliqueEdges_mem_iff] at he
  obtain ⟨p, q, hp, hq, hep, heq, _⟩ := he
  refine ⟨?_, ?_⟩
  · rw [hep]
    exact encodePosition_lt N p.1 p.2
      ((clausePositions_mem N p.1 p.2).mp hp).1
      (clausePos_li_lt_posBase N p.1 p.2 hp)
  · rw [heq]
    exact encodePosition_lt N q.1 q.2
      ((clausePositions_mem N q.1 q.2).mp hq).1
      (clausePos_li_lt_posBase N q.1 q.2 hq)

private theorem fgraph_wf_instance (N : cnf) :
    fgraph_wf (N.length * positionBase N, cliqueEdges N) :=
  fun e he => cliqueEdges_endpoints_lt N e he

------------------------------------------------------------------------
-- §13  FlatClique of the no-instance is False
------------------------------------------------------------------------

private theorem noCliqueInstance_not_FlatClique : ¬ FlatClique noCliqueInstance := by
  simp only [FlatClique, noCliqueInstance, isfKClique, isfClique, list_ofFlatType]
  rintro ⟨l, _, ⟨⟨htype, _, _⟩, hlen⟩⟩
  rcases l with _ | ⟨v, _ | _⟩
  · simp at hlen
  · simp at hlen
    exact absurd (htype v List.mem_cons_self) (Nat.not_lt_zero v)
  · simp at hlen

------------------------------------------------------------------------
-- §14  Forward direction: SAT N → FlatClique (instance N)
------------------------------------------------------------------------

private theorem sat_to_clique (N : cnf) (hSAT : SAT N) :
    FlatClique (kSAT_to_FlatClique_instance N) := by
  obtain ⟨a, hsat⟩ := hSAT
  have hExists : ∀ ci, ci < N.length →
      ∃ li, li < (N.getD ci []).length ∧
        evalLiteral a ((N.getD ci []).getD li (true, 0)) = true := fun ci hci => by
    have heval := (evalCnf_clause_iff a N).mp hsat (N.getD ci []) (getD_mem N ci [] hci)
    simp only [evalClause] at heval
    exact any_to_exists_index _ (evalLiteral a) heval
  let fi : ∀ ci, ci < N.length → Nat := fun ci hci => (hExists ci hci).choose
  have hfi_lt : ∀ ci (hci : ci < N.length), fi ci hci < (N.getD ci []).length :=
    fun ci hci => (hExists ci hci).choose_spec.1
  have hfi_eval : ∀ ci (hci : ci < N.length),
      evalLiteral a ((N.getD ci []).getD (fi ci hci) (true, 0)) = true :=
    fun ci hci => (hExists ci hci).choose_spec.2
  let clique : List Nat :=
    (List.finRange N.length).map (fun ⟨ci, hci⟩ => encodePosition N (ci, fi ci hci))
  refine ⟨clique, fgraph_wf_instance N, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- list_ofFlatType
    intro v hv
    simp only [clique, List.mem_map, List.mem_finRange] at hv
    obtain ⟨⟨ci, hci⟩, _, rfl⟩ := hv
    exact encodePosition_lt N ci (fi ci hci) hci
      (Nat.lt_trans (hfi_lt ci hci)
        (positionBase_gt_clauseLen N (N.getD ci []) (getD_mem N ci [] hci)))
  · -- Nodup
    show ((List.finRange N.length).map
        (fun ⟨ci, hci⟩ => encodePosition N (ci, fi ci hci))).Nodup
    refine List.Nodup.map ?_ (List.nodup_finRange N.length)
    intro ⟨ci₁, hci₁⟩ ⟨ci₂, hci₂⟩ henc
    have hli₁ := Nat.lt_trans (hfi_lt ci₁ hci₁)
      (positionBase_gt_clauseLen N (N.getD ci₁ []) (getD_mem N ci₁ [] hci₁))
    have hli₂ := Nat.lt_trans (hfi_lt ci₂ hci₂)
      (positionBase_gt_clauseLen N (N.getD ci₂ []) (getD_mem N ci₂ [] hci₂))
    simp only [Fin.mk.injEq]
    exact (encodePosition_inj N ci₁ _ ci₂ _ hli₁ hli₂ henc).1
  · -- All pairs connected
    intro v₁ v₂ hv₁ hv₂ hne
    simp only [clique, List.mem_map, List.mem_finRange] at hv₁ hv₂
    obtain ⟨⟨ci₁, hci₁⟩, _, rfl⟩ := hv₁
    obtain ⟨⟨ci₂, hci₂⟩, _, rfl⟩ := hv₂
    have hciNe : ci₁ ≠ ci₂ := fun heq => hne (by simp [heq])
    let li₁ := fi ci₁ hci₁
    let li₂ := fi ci₂ hci₂
    have hli₁_lt := Nat.lt_trans (hfi_lt ci₁ hci₁)
      (positionBase_gt_clauseLen N (N.getD ci₁ []) (getD_mem N ci₁ [] hci₁))
    have hli₂_lt := Nat.lt_trans (hfi_lt ci₂ hci₂)
      (positionBase_gt_clauseLen N (N.getD ci₂ []) (getD_mem N ci₂ [] hci₂))
    rw [cliqueEdges_mem_iff]
    refine ⟨(ci₁, li₁), (ci₂, li₂),
      (clausePositions_mem N ci₁ li₁).mpr ⟨hci₁, hfi_lt ci₁ hci₁⟩,
      (clausePositions_mem N ci₂ li₂).mpr ⟨hci₂, hfi_lt ci₂ hci₂⟩,
      rfl, rfl, ?_⟩
    simp only [positionCompatible, bne_iff_ne, Bool.and_eq_true]
    refine ⟨hciNe, ?_⟩
    rw [literalAt_eq_some N ci₁ li₁ hci₁ (hfi_lt ci₁ hci₁),
        literalAt_eq_some N ci₂ li₂ hci₂ (hfi_lt ci₂ hci₂)]
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hNeg
    simp only [literalsAreNegations, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
               literalVar, literalPolarity] at hNeg
    have heval₁ : evalLiteral a ((N.getD ci₁ []).getD li₁ (true, 0)) = true := hfi_eval ci₁ hci₁
    have heval₂ : evalLiteral a ((N.getD ci₂ []).getD li₂ (true, 0)) = true := hfi_eval ci₂ hci₂
    generalize hl1 : (N.getD ci₁ []).getD li₁ (true, 0) = lit₁ at hNeg heval₁
    generalize hl2 : (N.getD ci₂ []).getD li₂ (true, 0) = lit₂ at hNeg heval₂
    obtain ⟨pol₁, var₁⟩ := lit₁
    obtain ⟨pol₂, var₂⟩ := lit₂
    obtain ⟨hVar, hPol⟩ := hNeg
    subst hVar
    simp only [evalLiteral, decide_eq_true_eq] at heval₁ heval₂
    exact hPol (heval₁.symm.trans heval₂)
  · simp [clique, List.length_map, List.length_finRange]

------------------------------------------------------------------------
-- §15  Backward direction: FlatClique (instance N) → SAT N
------------------------------------------------------------------------

/-- A nonempty clause is always satisfiable. -/
private theorem nonempty_clause_sat (C : clause) (hC : 0 < C.length) : SAT [C] := by
  rcases C with _ | ⟨⟨pol, v⟩, rest⟩
  · exact absurd hC (by simp)
  · let a : assgn := if pol then [v] else []
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, List.all_nil, Bool.and_true,
               evalClause, List.any_cons, evalLiteral, a]
    cases pol <;> simp [evalVar]

/-- Given clique size ≥ 2, extract a satisfying assignment. -/
private theorem clique_to_sat_of_length_ge_two (N : cnf) (hN2 : 2 ≤ N.length)
    (l : List fvertex)
    (hnodup : l.Nodup)
    (hadj : ∀ v₁ v₂, v₁ ∈ l → v₂ ∈ l → v₁ ≠ v₂ → (v₁, v₂) ∈ cliqueEdges N)
    (hlen : l.length = N.length) : SAT N := by
  -- For each vertex in the clique, find its clause-literal position.
  have hDecode : ∀ v ∈ l, ∃ p ∈ clausePositions N, v = encodePosition N p := by
    intro v hv
    -- Pick another distinct vertex (exists since |l| ≥ 2 and Nodup).
    have hother : ∃ w ∈ l, w ≠ v := by
      rcases l with _ | ⟨a, _ | ⟨b, _⟩⟩
      · simp only [List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ⟨b, by simp, by
              intro heq; subst heq
              exact (List.nodup_cons.mp hnodup).1 List.mem_cons_self⟩
        · exact ⟨a, by simp, by
              intro heq; subst heq
              rcases hv with rfl | hv
              · exact (List.nodup_cons.mp hnodup).1 List.mem_cons_self
              · exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem _ hv)⟩
    obtain ⟨w, hw, hne⟩ := hother
    have hedge := hadj v w hv hw hne.symm
    rw [cliqueEdges_mem_iff] at hedge
    obtain ⟨p, _, hp, _, rfl, _, _⟩ := hedge
    exact ⟨p, hp, rfl⟩
  -- Map each vertex to its clause index.
  have hciDistinct : ∀ v w, v ∈ l → w ∈ l → v ≠ w →
      v / positionBase N ≠ w / positionBase N := by
    intro v w hv hw hne
    obtain ⟨p, hp, hveq⟩ := hDecode v hv
    obtain ⟨q, hq, hweq⟩ := hDecode w hw
    have hedge := hadj v w hv hw hne
    rw [cliqueEdges_mem_iff] at hedge
    obtain ⟨p', q', hp', hq', hvp', hwq', hcompat⟩ := hedge
    have hpbase := clausePos_li_lt_posBase N p.1 p.2 hp
    have hqbase := clausePos_li_lt_posBase N q.1 q.2 hq
    obtain ⟨hci, hli⟩ := encodePosition_inj N p.1 p.2 p'.1 p'.2 hpbase
      (clausePos_li_lt_posBase N p'.1 p'.2 hp') (hveq ▸ hvp')
    have hpp' : p = p' := Prod.ext hci hli
    subst hpp'
    rw [hveq, encodePosition_div N p.1 p.2 hpbase]
    obtain ⟨hci', hli'⟩ := encodePosition_inj N q.1 q.2 q'.1 q'.2 hqbase
      (clausePos_li_lt_posBase N q'.1 q'.2 hq') (hweq ▸ hwq')
    have hqq' : q = q' := Prod.ext hci' hli'
    subst hqq'
    rw [hweq, encodePosition_div N q.1 q.2 hqbase]
    exact positionCompatible_clause_ne N p q hcompat
  -- All clause indices lie in {0,..,N.length-1}.
  have hciRange : ∀ v ∈ l, v / positionBase N < N.length := by
    intro v hv
    obtain ⟨p, hp, hveq⟩ := hDecode v hv
    rw [hveq, encodePosition_div N p.1 p.2 (clausePos_li_lt_posBase N p.1 p.2 hp)]
    exact (clausePositions_mem N p.1 p.2).mp hp |>.1
  -- The N.length distinct clause indices cover all of {0,..,N.length-1}.
  have hciSurj : ∀ ci < N.length, ∃ v ∈ l, v / positionBase N = ci := by
    intro ci hci
    by_contra h
    push_neg at h
    -- l.map (· / positionBase N) is Nodup of length N.length inside {0,..,N.length-1}
    -- but doesn't contain ci, contradicting length = N.length.
    have hmapNodup : (l.map (· / positionBase N)).Nodup := by
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      by_contra hne
      exact hciDistinct x y hx hy hne hxy
    have hmapLen : (l.map (· / positionBase N)).length = N.length := by
      rw [List.length_map]; exact hlen
    -- Use Finset pigeonhole
    have hcard : (l.map (· / positionBase N)).toFinset.card = N.length := by
      rw [List.toFinset_card_of_nodup hmapNodup, hmapLen]
    have hsub : (l.map (· / positionBase N)).toFinset ⊆ (Finset.range N.length).erase ci := by
      intro x hx
      simp only [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨fun heq => h v hv heq, hciRange v hv⟩
    have hcard2 : ((Finset.range N.length).erase ci).card = N.length - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hci), Finset.card_range]
    have hcontra : N.length ≤ N.length - 1 := by
      have := Finset.card_le_card hsub
      rw [hcard, hcard2] at this
      exact this
    omega
  -- Build satisfying assignment.
  let a : assgn := l.filterMap fun v =>
    match literalAt N (v / positionBase N) (v % positionBase N) with
    | some (true, var) => some var
    | _ => none
  refine ⟨a, (evalCnf_clause_iff a N).mpr (fun C hC => ?_)⟩
  -- Find ci such that N.getD ci [] = C.
  rw [List.mem_iff_get] at hC
  obtain ⟨⟨ci, hci⟩, hget⟩ := hC
  -- Get the vertex v covering clause ci.
  obtain ⟨v, hv, hciV⟩ := hciSurj ci hci
  obtain ⟨p, hp, hveq⟩ := hDecode v hv
  have hpbase := clausePos_li_lt_posBase N p.1 p.2 hp
  have hpci := (clausePositions_mem N p.1 p.2).mp hp
  -- p.1 = ci
  have hpciEq : p.1 = ci := by
    rw [hveq, encodePosition_div N p.1 p.2 hpbase] at hciV; exact hciV
  -- The literal at (ci, p.2).
  have hpliLt : p.2 < (N.getD ci []).length := hpciEq ▸ hpci.2
  have hlitEq := literalAt_eq_some N ci p.2 hci hpliLt
  set lit := (N.getD ci []).getD p.2 (true, 0) with hlit_def
  rw [evalClause_literal_iff]
  -- N.getD ci [] = C (from hget and getD_eq_get).
  have hNgetD : N.getD ci [] = C := by
    rwa [getD_eq_get N ci [] hci]
  refine ⟨lit, ?_, ?_⟩
  · rw [← hNgetD]
    exact getD_mem (N.getD ci []) p.2 (true, 0) hpliLt
  · -- Show evalLiteral a lit = true.
    rcases lit with ⟨pol, var⟩
    simp only [evalLiteral, decide_eq_true_eq]
    rcases pol with _ | _
    · -- pol = false: need evalVar a var = false
      simp only [evalVar, decide_eq_false_iff_not, not_exists, not_and]
      -- If var ∈ a, then some v' ∈ l contributed (true, var), meaning literal (true, var) at v'.
      -- That literal and (false, var) are negations, contradicting positionCompatible.
      intro hmem
      simp only [a, List.mem_filterMap] at hmem
      obtain ⟨v', hv', hmatch⟩ := hmem
      obtain ⟨p', hp', hv'eq⟩ := hDecode v' hv'
      have hp'base := clausePos_li_lt_posBase N p'.1 p'.2 hp'
      have hlitV' : literalAt N (v' / positionBase N) (v' % positionBase N) = some (true, var) := by
        rcases h : literalAt N (v' / positionBase N) (v' % positionBase N) with _ | ⟨_ | _, w⟩
          <;> simp [h] at hmatch ⊢
        exact hmatch
      rw [hv'eq, encodePosition_div N p'.1 p'.2 hp'base,
          encodePosition_mod N p'.1 p'.2 hp'base] at hlitV'
      have hv'ne : v' ≠ v := by
        intro heq; subst heq
        have hpp' : p = p' := by
          have heq_enc : encodePosition N p = encodePosition N p' := hveq.symm.trans hv'eq
          obtain ⟨hcc, hll⟩ := encodePosition_inj N p.1 p.2 p'.1 p'.2 hpbase hp'base heq_enc
          exact Prod.ext hcc hll
        subst hpp'
        rw [← hpciEq] at hlitEq
        rw [hlitEq] at hlitV'
        simp at hlitV'
      have hedge := hadj v v' hv hv' (Ne.symm hv'ne)
      rw [cliqueEdges_mem_iff] at hedge
      obtain ⟨px, py, hpx, hpy, hvpx, hv'py, hcompat⟩ := hedge
      -- Decode px from v
      have hpxbase := clausePos_li_lt_posBase N px.1 px.2 hpx
      obtain ⟨hcipx, hlipx⟩ := encodePosition_inj N p.1 p.2 px.1 px.2 hpbase hpxbase
        (hveq ▸ hvpx)
      have hpxEq : px = p := Prod.ext hcipx.symm hlipx.symm
      -- Decode py from v'
      have hpybase := clausePos_li_lt_posBase N py.1 py.2 hpy
      obtain ⟨hcipy, hlipy⟩ := encodePosition_inj N p'.1 p'.2 py.1 py.2 hp'base hpybase
        (hv'eq ▸ hv'py)
      have hpyEq : py = p' := Prod.ext hcipy.symm hlipy.symm
      -- Rewrite hcompat in terms of p, p'
      rw [hpxEq, hpyEq] at hcompat
      have hNotNeg := positionCompatible_not_neg N p p' hcompat (false, var) (true, var)
        (hpciEq ▸ hlitEq) hlitV'
      simp [literalsAreNegations, literalVar, literalPolarity] at hNotNeg
    · -- pol = true: need evalVar a var = true, i.e., var ∈ a
      simp only [evalVar, decide_eq_true_eq]
      simp only [a, List.mem_filterMap]
      refine ⟨v, hv, ?_⟩
      rw [hveq, encodePosition_div N p.1 p.2 hpbase,
          encodePosition_mod N p.1 p.2 hpbase, hpciEq, hlitEq]

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
      rcases Nat.lt_or_ge N.length 2 with hlt2 | hge2
      · rcases N with _ | ⟨C, _ | ⟨D, rest⟩⟩
        · exact ⟨[], by simp [satisfiesCnf, evalCnf]⟩
        · have hCpos : 0 < C.length := by
            have := ((kCNF_clause_length k [C]).mp hkCNF) C List.mem_cons_self
            omega
          exact nonempty_clause_sat C hCpos
        · simp only [List.length_cons] at hlt2; omega
      · obtain ⟨l, _, ⟨⟨_, hnodup, hadj⟩, hlen⟩⟩ := hClique
        exact clique_to_sat_of_length_ge_two N hge2 l hnodup hadj hlen
  · simp only [hcond, ↓reduceIte]
    exact ⟨fun ⟨hk, hkCNF, _⟩ => absurd ⟨hk, hkCNF⟩ hcond,
           fun h => absurd h noCliqueInstance_not_FlatClique⟩

------------------------------------------------------------------------
-- §17  Size bound helpers
------------------------------------------------------------------------

private theorem encodable_size_list_ge_length {α : Type} [encodable α] (l : List α) :
    l.length ≤ encodable.size l := by
  induction l with
  | nil => simp [encodable.size]
  | cons x xs ih =>
    rw [encodable_size_list_cons]; simp only [List.length_cons]; omega

private theorem cnf_length_le_size (N : cnf) : N.length ≤ encodable.size N :=
  encodable_size_list_ge_length N

private theorem positionBase_le_size_add_one (N : cnf) :
    positionBase N ≤ encodable.size N + 1 := by
  simp only [positionBase]
  suffices h : N.foldr (fun C acc => Nat.max C.length acc) 0 ≤ encodable.size N by omega
  induction N with
  | nil => simp [encodable.size]
  | cons C Cs ih =>
    simp only [List.foldr, encodable_size_list_cons]
    apply Nat.max_le.mpr
    exact ⟨Nat.le_trans (encodable_size_list_ge_length C) (by omega),
           Nat.le_trans ih (by omega)⟩

private theorem clausePositionsAux_length_base_indep (N : cnf) (b₁ b₂ : Nat) :
    (clausePositionsAux N b₁).length = (clausePositionsAux N b₂).length := by
  induction N generalizing b₁ b₂ with
  | nil => rfl
  | cons C Cs ih =>
    simp only [clausePositionsAux, List.length_append, List.length_map, List.length_range]
    exact congrArg _ (ih _ _)

private theorem clausePositions_length_le_size (N : cnf) :
    (clausePositions N).length ≤ encodable.size N := by
  simp only [clausePositions]
  induction N with
  | nil => simp [clausePositionsAux, encodable.size]
  | cons C Cs ih =>
    simp only [clausePositionsAux, List.length_append, List.length_map, List.length_range,
               encodable_size_list_cons]
    calc C.length + (clausePositionsAux Cs 1).length
        = C.length + (clausePositionsAux Cs 0).length := by
            rw [clausePositionsAux_length_base_indep Cs 1 0]
      _ ≤ encodable.size C + encodable.size Cs := by
            exact Nat.add_le_add (encodable_size_list_ge_length C) ih
      _ ≤ encodable.size C + 1 + encodable.size Cs := by omega

private theorem encodable_size_fedge_list_bounded (B : Nat) (edges : List fedge)
    (hbound : ∀ e ∈ edges, e.1 < B ∧ e.2 < B) :
    encodable.size edges ≤ edges.length * (2 * B + 2) := by
  induction edges with
  | nil => simp [encodable.size]
  | cons e es ih =>
    obtain ⟨e1, e2⟩ := e
    obtain ⟨h1, h2⟩ : e1 < B ∧ e2 < B := hbound (e1, e2) List.mem_cons_self
    have ihb := ih (fun e' he' => hbound e' (List.mem_cons_of_mem (e1, e2) he'))
    rw [encodable_size_list_cons]
    have he1 : e1 ≤ B := Nat.le_of_lt h1
    have he2 : e2 ≤ B := Nat.le_of_lt h2
    have hsum : e1 + e2 ≤ B + B := Nat.add_le_add he1 he2
    have hesize : encodable.size (e1, e2) + 1 ≤ 2 * B + 2 := by
      show e1 + e2 + 1 + 1 ≤ 2 * B + 2
      calc e1 + e2 + 1 + 1
          = (e1 + e2) + 2 := by ring
        _ ≤ (B + B) + 2 := Nat.add_le_add_right hsum 2
        _ = 2 * B + 2 := by ring
    calc encodable.size (e1, e2) + 1 + encodable.size es
        ≤ (2 * B + 2) + es.length * (2 * B + 2) := Nat.add_le_add hesize ihb
      _ = (es.length + 1) * (2 * B + 2) := by ring
      _ = ((e1, e2) :: es).length * (2 * B + 2) := by rw [List.length_cons]

private theorem cliqueEdges_length_le (N : cnf) :
    (cliqueEdges N).length ≤ (clausePositions N).length ^ 2 := by
  show ((clausePositions N).flatMap (addCompatibleEdges N (clausePositions N))).length ≤ _
  rw [List.length_flatMap]
  have hbound : ∀ x ∈ (clausePositions N).map
      (fun p => (addCompatibleEdges N (clausePositions N) p).length),
        x ≤ (clausePositions N).length := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    show (((clausePositions N).filter (positionCompatible N p)).map _).length ≤ _
    rw [List.length_map]
    exact List.length_filter_le _ _
  calc ((clausePositions N).map
          (fun p => (addCompatibleEdges N (clausePositions N) p).length)).sum
      ≤ ((clausePositions N).map
          (fun p => (addCompatibleEdges N (clausePositions N) p).length)).length
            * (clausePositions N).length :=
            List.sum_le_card_nsmul _ _ hbound
    _ = (clausePositions N).length * (clausePositions N).length := by rw [List.length_map]
    _ = (clausePositions N).length ^ 2 := by ring

private theorem nat_le_self_sq (n : Nat) : n ≤ n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.le_refl 0
  · calc n = n * 1 := (Nat.mul_one _).symm
      _ ≤ n * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 2 := by ring

private theorem nat_sq_le_pow_four (n : Nat) : n ^ 2 ≤ n ^ 4 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.le_refl 0
  · exact Nat.pow_le_pow_right hn (by decide : 2 ≤ 4)

private theorem nat_cube_le_pow_four (n : Nat) : n ^ 3 ≤ n ^ 4 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.le_refl 0
  · exact Nat.pow_le_pow_right hn (by decide : 3 ≤ 4)

private theorem encodable_size_cliqueEdges_le (N : cnf) :
    encodable.size (cliqueEdges N) ≤ 6 * (encodable.size N) ^ 4 + 6 := by
  set S := encodable.size N
  have hNlenS : N.length ≤ S := cnf_length_le_size N
  have hpbaseS : positionBase N ≤ S + 1 := positionBase_le_size_add_one N
  have hcpS : (clausePositions N).length ≤ S := clausePositions_length_le_size N
  have hNumEdges : (cliqueEdges N).length ≤ S ^ 2 :=
    Nat.le_trans (cliqueEdges_length_le N) (Nat.pow_le_pow_left hcpS 2)
  have hSizeBound := encodable_size_fedge_list_bounded (N.length * positionBase N)
    (cliqueEdges N) (fun e he => cliqueEdges_endpoints_lt N e he)
  have hMul : N.length * positionBase N ≤ S ^ 2 + S := by
    calc N.length * positionBase N
        ≤ S * (S + 1) := Nat.mul_le_mul hNlenS hpbaseS
      _ = S ^ 2 + S := by ring
  have hBbound : 2 * (N.length * positionBase N) + 2 ≤ 2 * S ^ 2 + 2 * S + 2 := by linarith
  have hS2_le_S4 : S ^ 2 ≤ S ^ 4 := nat_sq_le_pow_four S
  have hS3_le_S4 : S ^ 3 ≤ S ^ 4 := nat_cube_le_pow_four S
  calc encodable.size (cliqueEdges N)
      ≤ (cliqueEdges N).length * (2 * (N.length * positionBase N) + 2) := hSizeBound
    _ ≤ S ^ 2 * (2 * S ^ 2 + 2 * S + 2) := Nat.mul_le_mul hNumEdges hBbound
    _ = 2 * S ^ 4 + 2 * S ^ 3 + 2 * S ^ 2 := by ring
    _ ≤ 6 * S ^ 4 + 6 := by linarith

private theorem kSAT_to_FlatClique_f_size_bound (k : Nat) (N : cnf) :
    encodable.size (kSAT_to_FlatClique_f k N) ≤ 10 * (encodable.size N) ^ 4 + 10 := by
  unfold kSAT_to_FlatClique_f
  by_cases hcond : 0 < k ∧ kCNF k N
  · rw [if_pos hcond]
    show encodable.size (kSAT_to_FlatClique_instance N) ≤ _
    unfold kSAT_to_FlatClique_instance
    set S := encodable.size N
    have hNlenS : N.length ≤ S := cnf_length_le_size N
    have hpbaseS : positionBase N ≤ S + 1 := positionBase_le_size_add_one N
    have hCE : encodable.size (cliqueEdges N) ≤ 6 * S ^ 4 + 6 := encodable_size_cliqueEdges_le N
    have hTotal : encodable.size ((N.length * positionBase N, cliqueEdges N), N.length) =
        N.length * positionBase N + encodable.size (cliqueEdges N) + N.length + 2 := by
      show (N.length * positionBase N + encodable.size (cliqueEdges N) + 1) + N.length + 1 = _
      ring
    rw [hTotal]
    have hMul : N.length * positionBase N ≤ S ^ 2 + S := by
      calc N.length * positionBase N
          ≤ S * (S + 1) := Nat.mul_le_mul hNlenS hpbaseS
        _ = S ^ 2 + S := by ring
    have hS_le_sq : S ≤ S ^ 2 := nat_le_self_sq S
    have hS2_le_S4 : S ^ 2 ≤ S ^ 4 := nat_sq_le_pow_four S
    linarith
  · rw [if_neg hcond]
    show encodable.size noCliqueInstance ≤ _
    show (3 : Nat) ≤ 10 * (encodable.size N) ^ 4 + 10
    calc (3 : Nat) ≤ 10 := by decide
      _ ≤ 10 * (encodable.size N) ^ 4 + 10 := Nat.le_add_left _ _

------------------------------------------------------------------------
-- §18  Main polynomial-time reduction theorem
------------------------------------------------------------------------

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique :=
  ⟨⟨kSAT_to_FlatClique_f k,
    ⟨⟨fun n => 10 * n ^ 4 + 10,
      by apply inOPoly_add
         · exact ⟨4, ⟨10, 1, fun n hn => by nlinarith [Nat.one_le_pow 4 n (by omega)]⟩⟩
         · exact inOPoly_const 10,
      by intro a b hab; nlinarith [Nat.pow_le_pow_left hab 4],
      kSAT_to_FlatClique_f_size_bound k⟩⟩,
    fun {N} => kSAT_to_FlatClique_f_correct k N⟩⟩
