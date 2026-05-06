import Complexity.Complexity.NP
import Complexity.NP.kSAT
import Complexity.NP.FlatClique

set_option autoImplicit false

def clausePositionsAux : List clause → Nat → List (Nat × Nat)
  | [], _ => []
  | C :: Cs, ci =>
      (List.range C.length).map (fun li => (ci, li)) ++ clausePositionsAux Cs (ci + 1)

def clausePositions (N : cnf) : List (Nat × Nat) :=
  clausePositionsAux N 0

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
  (positions.filter (positionCompatible N p)).map (fun q => (encodePosition N p, encodePosition N q))

def cliqueVertices (N : cnf) : List Nat :=
  (clausePositions N).map (encodePosition N)

def cliqueEdges (N : cnf) : List fedge :=
  let positions := clausePositions N
  positions.flatMap (addCompatibleEdges N positions)

def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  (((cliqueVertices N).length, cliqueEdges N), N.length)

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique := by
  refine ⟨⟨kSAT_to_FlatClique_instance, trivial, fun {x} => ?_⟩⟩
  sorry
