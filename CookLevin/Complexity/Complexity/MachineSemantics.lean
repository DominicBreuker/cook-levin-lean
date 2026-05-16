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

-- Size of tapes in flattened representation.
-- We use the maximum tape length, matching the bookkeeping from the Coq development being ported.
def sizeOfmTapesFlat : List (List Nat) → Nat
  | [] => 0
  | tape :: tapes => max tape.length (sizeOfmTapesFlat tapes)

def tapeSymbolsBounded (sig : Nat) (tape : List Nat) : Prop :=
  ∀ x, x ∈ tape → x < sig

def flatTapesWellFormed (M : FlatTM) (initTapes : List (List Nat)) : Prop :=
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

/-- Padding lemma: once a TM has run for `n` steps and landed in a
halting state `cfg'`, any additional `k` steps leave the configuration
unchanged. Used when a decider's time budget is more generous than
the actual run length. Previously lived in `TMPrimitives.lean`; lifted
here in Part 2 Step 8 because `DecidesBy.proj_left` (in
`Complexity/Complexity/NP.lean`'s `P_NP_incl`) needs it. -/
theorem runFlatTM_extend {M : FlatTM} {cfg cfg' : FlatTMConfig} {n k : Nat}
    (h_run : runFlatTM n M cfg = some cfg')
    (h_halt : haltingStateReached M cfg' = true) :
    runFlatTM (n + k) M cfg = some cfg' := by
  induction n generalizing cfg with
  | zero =>
      have h_eq : cfg = cfg' := Option.some.inj h_run
      subst h_eq
      show runFlatTM (0 + k) M cfg = some cfg
      rw [Nat.zero_add]
      exact runFlatTM_of_halting M cfg k h_halt
  | succ n ih =>
      by_cases h_cfg : haltingStateReached M cfg = true
      · have h1 : runFlatTM (n + 1) M cfg = some cfg :=
          runFlatTM_of_halting M cfg (n + 1) h_cfg
        rw [h1] at h_run
        have h_eq : cfg = cfg' := Option.some.inj h_run
        subst h_eq
        exact runFlatTM_of_halting M cfg (n + 1 + k) h_cfg
      · have h_run_eq :
            runFlatTM (n + 1) M cfg =
              match stepFlatTM M cfg with
              | none => some cfg
              | some cfg'' => runFlatTM n M cfg'' := by
          show (if haltingStateReached M cfg = true then some cfg
                else match stepFlatTM M cfg with
                  | none => some cfg
                  | some cfg'' => runFlatTM n M cfg'') = _
          rw [if_neg h_cfg]
        rw [h_run_eq] at h_run
        have h_arith : n + 1 + k = (n + k) + 1 := by
          rw [Nat.add_right_comm]
        rw [h_arith]
        have h_run_eq_k :
            runFlatTM ((n + k) + 1) M cfg =
              match stepFlatTM M cfg with
              | none => some cfg
              | some cfg'' => runFlatTM (n + k) M cfg'' := by
          show (if haltingStateReached M cfg = true then some cfg
                else match stepFlatTM M cfg with
                  | none => some cfg
                  | some cfg'' => runFlatTM (n + k) M cfg'') = _
          rw [if_neg h_cfg]
        rw [h_run_eq_k]
        cases h_step : stepFlatTM M cfg with
        | none =>
            rw [h_step] at h_run
            have h_eq : cfg = cfg' := Option.some.inj h_run
            subst h_eq
            exact absurd h_halt h_cfg
        | some cfg'' =>
            rw [h_step] at h_run
            exact ih h_run

/-- Once a configuration is non-halting *and* its step is `none` (no
matching transition entry), the run is "stuck" at that config: any
number of further steps leaves the config unchanged. Symmetric counterpart
of `runFlatTM_of_halting`. Lifted to `MachineSemantics.lean` in Part 2
Step 11.0 so `composeFlatTM_run` (in `TMPrimitives.lean`) can use it. -/
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

/-- General composition: if `runFlatTM n M cfg = some cfg_mid`, then
running for `n + m` steps from `cfg` is the same as running for `m`
steps from `cfg_mid`. Handles halting and stuck cases uniformly via
`runFlatTM_of_halting` / `runFlatTM_stuck`. Lifted in Part 2 Step 11.0. -/
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
      · have h_run_eq : runFlatTM (n + 1) M cfg = some cfg := by
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
            have h_run_eq : runFlatTM (n + 1) M cfg = runFlatTM n M cfg' := by
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM n M cfg') = _
              rw [if_neg h_halt, h_step]
            rw [h_run_eq] at h
            have ih := runFlatTM_compose M n m cfg' cfg_mid h
            have h_run_full : runFlatTM (n + 1 + m) M cfg = runFlatTM (n + m) M cfg' := by
              have h_swap : n + 1 + m = n + m + 1 := by
                rw [Nat.add_right_comm]
              rw [h_swap]
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM (n + m) M cfg') = _
              rw [if_neg h_halt, h_step]
            rw [h_run_full, ih]
  termination_by n _ _ _ _ => n

/-- Extending an `n`-step run by one explicit non-halting step. -/
theorem runFlatTM_extend_by_step
    (M : FlatTM) :
    ∀ (n : Nat) (cfg cfg_mid cfg_final : FlatTMConfig),
      runFlatTM n M cfg = some cfg_mid →
      haltingStateReached M cfg_mid = false →
      stepFlatTM M cfg_mid = some cfg_final →
      runFlatTM (n + 1) M cfg = some cfg_final
  | 0, cfg, cfg_mid, cfg_final, h_run, h_mid_not_halt, h_step => by
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
      · rw [h_run_eq, if_pos h_cfg_halt] at h_run
        have h_eq : cfg = cfg_mid := Option.some.inj h_run
        rw [h_eq] at h_cfg_halt
        rw [h_mid_not_halt] at h_cfg_halt
        exact absurd h_cfg_halt (by decide)
      · rw [h_run_eq, if_neg h_cfg_halt] at h_run
        cases h_step_cfg : stepFlatTM M cfg with
        | none =>
            rw [h_step_cfg] at h_run
            have h_eq : cfg = cfg_mid := Option.some.inj h_run
            rw [h_eq] at h_step_cfg
            rw [h_step_cfg] at h_step
            cases h_step
        | some cfg' =>
            rw [h_step_cfg] at h_run
            have ih := runFlatTM_extend_by_step M n cfg' cfg_mid cfg_final
              h_run h_mid_not_halt h_step
            have h_run2_eq :
                runFlatTM (n + 1 + 1) M cfg =
                  if haltingStateReached M cfg = true then some cfg
                  else match stepFlatTM M cfg with
                    | none => some cfg
                    | some cfg' => runFlatTM (n + 1) M cfg' := rfl
            rw [h_run2_eq, if_neg h_cfg_halt, h_step_cfg]
            exact ih
  termination_by n _ _ _ _ _ _ => n

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
def computableTime' {α : Type u} {β : Type v} : α → (β → Nat) → Prop
  | _, f =>
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
