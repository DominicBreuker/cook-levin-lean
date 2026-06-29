/-! # CliqueRel verifier design probe (top-down, Risk C2 / C7, 2026-06-29)

Design-level `#eval` validation of the **FlatClique verifier** `cliqueRelCmd`
BEFORE proof engineering (project methodology: probe before engineering). This
is the top-down analogue of `EvalCnfCmd` — the next decider to bring to the
sorry-free / axiom-clean state SAT's `evalCnfCmd` reached (HANDOFF top-down
"CliqueRelTM").

The verifier decides
  `cliqueRel (G,k) l = fgraph_wf G ∧ list_ofFlatType G.1 l ∧ l.Nodup
                        ∧ (∀ v₁ v₂ ∈ l, v₁≠v₂ → (v₁,v₂) ∈ G.2) ∧ l.length = k`
where `G = (numV, edges)`, `edges : List (Nat × Nat)`, `l : List Nat`.

This probe settles, at the register-arithmetic level (no real machines):

1. **A bit-level (`BitState`) unary, self-delimiting encoding round-trips.**
   Numbers are unary `1`-blocks; each value ends with a `0` terminator; lists
   carry a unary `replicate length 1` *tally* register (the `forBnd` loop bound,
   so no list-level end sentinel is needed — the EvalCnf CNF-stream pattern).
2. **The stream-parsing primitives the `Cmd` will use are realisable** — extract
   one unary value from a stream, and scan the edge stream for a pair (the
   membership test `(v₁,v₂) ∈ edges`).
3. **A reference verifier built only from those primitives agrees with
   `cliqueRel`** on clique / non-clique / malformed inputs — the go/no-go that
   the algorithm + encoding are mutually consistent.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/CliqueRelProbe.lean`
(every `#eval` must print `true`). -/

abbrev Reg := List Nat

def isBit (r : Reg) : Bool := r.all (· ≤ 1)

/-! ## Encoding (bit-level, unary, self-delimiting) -/

/-- A single number, unary with a `0` terminator: `replicate v 1 ++ [0]`. -/
def encNum (v : Nat) : Reg := List.replicate v 1 ++ [0]

/-- An edge `(a,b)` = two terminated unary numbers. -/
def encEdge (e : Nat × Nat) : Reg := encNum e.1 ++ encNum e.2

/-- The vertex stream = the vertices' terminated unary blocks, concatenated.
The loop bound is `replicate l.length 1` (separate tally register). -/
def encVerts (l : List Nat) : Reg := (l.map encNum).flatten

/-- The edge stream, concatenated; bound = `replicate edges.length 1`. -/
def encEdges (edges : List (Nat × Nat)) : Reg := (edges.map encEdge).flatten

/-! ## Parsing primitives (what the `Cmd` does to the streams) -/

/-- Read one terminated unary block off the front of a stream, returning the
value and the remaining stream. Models `forBnd … (head;tail; appendOne acc | end)`. -/
def readNum : Reg → Nat × Reg
  | [] => (0, [])               -- malformed: no terminator
  | 0 :: rest => (0, rest)      -- empty block, consume terminator
  | 1 :: rest => let (v, r) := readNum rest; (v + 1, r)
  | _ :: rest => (0, rest)      -- non-bit; shouldn't happen on a BitState

/-- Read `n` numbers off a stream (the vertex list, count from the tally). -/
def readNums : Nat → Reg → List Nat
  | 0, _ => []
  | n+1, s => let (v, r) := readNum s; v :: readNums n r

/-- Read `n` edges off a stream. -/
def readEdges : Nat → Reg → List (Nat × Nat)
  | 0, _ => []
  | n+1, s => let (a, r1) := readNum s; let (b, r2) := readNum r1;
              (a, b) :: readEdges n r2

/-! ## Reference verifier — operating on the encoded streams + tallies -/

/-- unary length compare: `a` and `b` (as unary `1`-blocks) represent equal Nats
iff equal lengths (`eqBit`). Here we already have the decoded counts. -/
def memEdge (a b : Nat) (edges : List (Nat × Nat)) : Bool :=
  edges.any (fun e => e.1 == a && e.2 == b)

/-- The verifier, reconstructing the structures from the streams the way the
`Cmd` will (parse, then the five AND-ed checks). -/
def refVerify (numV : Nat) (edgeStream : Reg) (nEdges : Nat)
    (k : Nat) (vertStream : Reg) (nVerts : Nat) : Bool :=
  let edges := readEdges nEdges edgeStream
  let l := readNums nVerts vertStream
  -- 1. fgraph_wf: every edge endpoint < numV
  let wf := edges.all (fun e => e.1 < numV && e.2 < numV)
  -- 2. list_ofFlatType numV l
  let ofType := l.all (· < numV)
  -- 3. Nodup
  let nodup := l.Nodup
  -- 4. clique: every distinct ordered pair is an edge
  let clique := l.all (fun v1 => l.all (fun v2 =>
                  if v1 == v2 then true else memEdge v1 v2 edges))
  -- 5. length = k
  let lenk := l.length == k
  wf && ofType && nodup && clique && lenk

/-! ## The spec (mirrors `FlatClique.cliqueRel`, decidable form) -/

def specCliqueRel (numV : Nat) (edges : List (Nat × Nat)) (k : Nat)
    (l : List Nat) : Bool :=
  let wf := edges.all (fun e => e.1 < numV && e.2 < numV)
  let ofType := l.all (· < numV)
  let nodup := l.Nodup
  let clique := l.all (fun v1 => l.all (fun v2 =>
                  if v1 == v2 then true else memEdge v1 v2 edges))
  let lenk := l.length == k
  wf && ofType && nodup && clique && lenk

/-! ## Test inputs -/

-- triangle on {0,1,2}, k=3, clique = [0,1,2] (directed edges both ways)
def edgesTri : List (Nat × Nat) :=
  [(0,1),(1,0),(0,2),(2,0),(1,2),(2,1)]
def numVTri : Nat := 3

-- a yes-instance
def lYes : List Nat := [0,1,2]
-- non-clique: missing edge usage (l includes vertex 2 but pretend only path 0-1-2)
def edgesPath : List (Nat × Nat) := [(0,1),(1,0),(1,2),(2,1)]
def lNo : List Nat := [0,1,2]   -- 0-2 not an edge ⇒ not a clique
-- Nodup violation
def lDup : List Nat := [0,1,1]
-- out of range
def lOOR : List Nat := [0,1,5]

/-! ## 1. encoding round-trips + bit-level -/

#eval isBit (encVerts lYes) && isBit (encEdges edgesTri)
#eval isBit (encNum 0) && isBit (encNum 4)
#eval readNums lYes.length (encVerts lYes) == lYes
#eval readNums lDup.length (encVerts lDup) == lDup
#eval readEdges edgesTri.length (encEdges edgesTri) == edgesTri
#eval readEdges edgesPath.length (encEdges edgesPath) == edgesPath
-- empty / zero-value edge cases
#eval readNums 1 (encVerts [0]) == [0]
#eval readEdges 1 (encEdges [(0,0)]) == [(0,0)]

/-! ## 2. the stream-driven verifier agrees with the spec -/

#eval refVerify numVTri (encEdges edgesTri) edgesTri.length 3
        (encVerts lYes) lYes.length
      == specCliqueRel numVTri edgesTri 3 lYes
#eval refVerify numVTri (encEdges edgesPath) edgesPath.length 3
        (encVerts lNo) lNo.length
      == specCliqueRel numVTri edgesPath 3 lNo
#eval refVerify numVTri (encEdges edgesTri) edgesTri.length 3
        (encVerts lDup) lDup.length
      == specCliqueRel numVTri edgesTri 3 lDup
#eval refVerify numVTri (encEdges edgesTri) edgesTri.length 3
        (encVerts lOOR) lOOR.length
      == specCliqueRel numVTri edgesTri 3 lOOR

/-! ## 3. the actual accept/reject values (eyeball) -/

#eval specCliqueRel numVTri edgesTri 3 lYes          -- expect true
#eval specCliqueRel numVTri edgesPath 3 lNo          -- expect false (0-2 not edge)
#eval specCliqueRel numVTri edgesTri 3 lDup          -- expect false (dup)
#eval specCliqueRel numVTri edgesTri 3 lOOR          -- expect false (oor + dup-free but 5≥3)
#eval specCliqueRel numVTri edgesTri 2 lYes          -- expect false (len≠k)

/-! ## 4. yes-instance accepts; the four no's reject -/

#eval specCliqueRel numVTri edgesTri 3 lYes == true
#eval specCliqueRel numVTri edgesPath 3 lNo == false
#eval specCliqueRel numVTri edgesTri 3 lDup == false
#eval specCliqueRel numVTri edgesTri 3 lOOR == false
#eval specCliqueRel numVTri edgesTri 2 lYes == false
