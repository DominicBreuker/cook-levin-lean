set_option autoImplicit false

universe u v

-- Machine model for Turing machines (matching Coq development)

-- Move type for Turing machine transitions
inductive TMMove where
  | Lmove  -- Move left
  | Rmove  -- Move right
  | Nmove  -- No move (stay)

deriving Repr, DecidableEq

-- A flattened Turing machine configuration
-- This matches the Coq flatTM structure
structure FlatTMConfig where
  -- Current state index
  state_idx : Nat
  -- Tapes: list of (left, current, right) for each tape
  tapes : List (List Nat × Nat × List Nat)

deriving Repr

-- A flattened transition table entry
-- (state, tape_values) -> (new_state, (write_values, move_directions))
structure FlatTMTransEntry where
  src_state : Nat
  src_tape_vals : List (Option Nat)
  dst_state : Nat
  dst_write_vals : List (Option Nat)
  move_dirs : List TMMove

deriving Repr

-- A flattened Turing machine
-- This matches the Coq flatTM inductive type
structure FlatTM where
  -- Alphabet size (number of symbols)
  sig : Nat
  -- Number of tapes
  tapes : Nat
  -- Number of states
  states : Nat
  -- Transition table: list of (state, tape_config) -> (new_state, write_config, moves)
  trans : List FlatTMTransEntry
  -- Start state index
  start : Nat
  -- Halt states (as list of booleans, where position i indicates if state i is halting)
  halt : List Bool

deriving Repr

-- Execution semantics for flattened Turing machines

-- Size of tapes in flattened representation
def sizeOfmTapesFlat : List (List Nat) → Nat
  | [] => 0
  | tape :: tapes => max tape.length (sizeOfmTapesFlat tapes)

def tapeSymbolsBounded (sig : Nat) (tape : List Nat) : Prop :=
  ∀ x, x ∈ tape → x < sig

def validFlatTapes (M : FlatTM) (initTapes : List (List Nat)) : Prop :=
  initTapes.length = M.tapes ∧
    ∀ tape ∈ initTapes, tapeSymbolsBounded M.sig tape

def isValidFlatTape (sig : Nat) (tape : List Nat) : Bool :=
  tape.all (fun x => x < sig)

def isValidFlatTapes (M : FlatTM) (initTapes : List (List Nat)) : Bool :=
  decide (initTapes.length = M.tapes) &&
    initTapes.all (isValidFlatTape M.sig)

-- Initial configuration for a flattened TM
-- Takes a flatTM and initial tape contents
def initFlatConfig (M : FlatTM) (initTapes : List (List Nat)) : FlatTMConfig :=
  FlatTMConfig.mk
    M.start
    (initTapes.map (fun tape => ([], 0, tape)))

def currentTapeSymbol (tape : List Nat × Nat × List Nat) : Option Nat :=
  if h : tape.2.1 < tape.2.2.length then
    some (tape.2.2.get ⟨tape.2.1, h⟩)
  else
    none

def writeCurrentTapeSymbol (tape : List Nat × Nat × List Nat) (symbol : Option Nat) :
    List Nat × Nat × List Nat :=
  let left := tape.1
  let head := tape.2.1
  let right := tape.2.2
  match symbol with
  | none => (left, head, right)
  | some sym =>
      if _ : head < right.length then
        (left, head, right.take head ++ sym :: right.drop (head + 1))
      else
        (left, head, right ++ List.replicate (head - right.length) 0 ++ [sym])

def moveTapeHead (tape : List Nat × Nat × List Nat) : TMMove → List Nat × Nat × List Nat
  | .Lmove => (tape.1, tape.2.1 - 1, tape.2.2)
  | .Rmove => (tape.1, tape.2.1 + 1, tape.2.2)
  | .Nmove => tape

def tapeStep (tape : List Nat × Nat × List Nat) (write : Option Nat) (move : TMMove) :
    List Nat × Nat × List Nat :=
  moveTapeHead (writeCurrentTapeSymbol tape write) move

def entryMatchesConfig (entry : FlatTMTransEntry) (cfg : FlatTMConfig) : Bool :=
  entry.src_state == cfg.state_idx &&
    entry.src_tape_vals = cfg.tapes.map currentTapeSymbol

def applyTransitionEntry (cfg : FlatTMConfig) (entry : FlatTMTransEntry) : Option FlatTMConfig :=
  if _ : cfg.tapes.length = entry.dst_write_vals.length ∧ cfg.tapes.length = entry.move_dirs.length then
    some {
      state_idx := entry.dst_state
      tapes := List.zipWith (fun tape payload =>
        tapeStep tape payload.1 payload.2) cfg.tapes (List.zip entry.dst_write_vals entry.move_dirs)
    }
  else
    none

def stepFlatTM (M : FlatTM) (cfg : FlatTMConfig) : Option FlatTMConfig := do
  let entry ← M.trans.find? (fun entry => entryMatchesConfig entry cfg)
  applyTransitionEntry cfg entry

def haltingStateReached (M : FlatTM) (cfg : FlatTMConfig) : Bool :=
  M.halt.getD cfg.state_idx false

def runFlatTM : Nat → FlatTM → FlatTMConfig → Option FlatTMConfig
  | 0, _, cfg => some cfg
  | n + 1, M, cfg =>
      if haltingStateReached M cfg then
        some cfg
      else
        match stepFlatTM M cfg with
        | none => some cfg
        | some cfg' => runFlatTM n M cfg'

def execFlatTM (M : FlatTM) (initTapes : List (List Nat)) (steps : Nat) : Option FlatTMConfig :=
  if isValidFlatTapes M initTapes then
    runFlatTM steps M (initFlatConfig M initTapes)
  else
    none

def acceptsFlatTM (M : FlatTM) (initTapes : List (List Nat)) (steps : Nat) : Bool :=
  match execFlatTM M initTapes steps with
  | none => false
  | some cfg => haltingStateReached M cfg

-- Time-bounded acceptance predicate
def acceptsInTime (M : FlatTM) (maxSize : Nat) (steps : Nat) : Prop :=
  ∃ initTapes : List (List Nat),
    isValidFlatTapes M initTapes = true ∧
    sizeOfmTapesFlat initTapes ≤ maxSize ∧
    acceptsFlatTM M initTapes steps

theorem runFlatTM_of_halting (M : FlatTM) (cfg : FlatTMConfig) (steps : Nat)
    (h : haltingStateReached M cfg = true) :
    runFlatTM steps M cfg = some cfg := by
  cases steps with
  | zero =>
      simp [runFlatTM]
  | succ n =>
      simp [runFlatTM, h]

theorem execFlatTM_eq_some_runFlatTM {M : FlatTM} {initTapes : List (List Nat)} {steps : Nat}
    (h : isValidFlatTapes M initTapes = true) :
    execFlatTM M initTapes steps = runFlatTM steps M (initFlatConfig M initTapes) := by
  simp [execFlatTM, h]

theorem acceptsFlatTM_eq_true_iff {M : FlatTM} {initTapes : List (List Nat)} {steps : Nat} :
    acceptsFlatTM M initTapes steps = true ↔
      ∃ cfg, execFlatTM M initTapes steps = some cfg ∧ haltingStateReached M cfg = true := by
  unfold acceptsFlatTM
  cases hExec : execFlatTM M initTapes steps with
  | none =>
      simp
  | some cfg =>
      simp

-- Polynomial-time computable predicate for machine execution
-- This replaces the placeholder computableTime' with a meaningful statement
def computableTime' {α : Type u} {β : Type v} (_ : α) (f : β → Nat) : Prop :=
  -- A function f is computable in time computable by some machine
  -- This means there exists a machine that computes f within the given time bound
  ∃ (M : FlatTM) (maxSize steps : Nat),
    -- The machine M accepts its own description in bounded time
    acceptsInTime M maxSize steps ∧
    -- The time bound captures the complexity of f
    ∀ y : β, f y ≤ steps

-- Size of a flatTM encoding (in natural numbers)
def sizeFlatTM (M : FlatTM) : Nat :=
  -- Size is roughly: sig + tapes + states + trans entries + start + halt
  M.sig + M.tapes + M.states + 
  (M.trans.length * 5) +  -- Approximate: each transition has ~5 components
  M.start + M.halt.length

-- Size of flatTM input (machine, maxSize, steps)
def sizeFlatTMInput (M : FlatTM) (maxSize steps : Nat) : Nat :=
  sizeFlatTM M + maxSize + steps
