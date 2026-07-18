import Complexity.NP.SAT.CookLevin.Reductions.FrontPieces

/-! # C8-3 probe — the front `Cmd` pieces against their pure models

`#eval` validation (probe-before-prove) of the three C8-3 building blocks in
`Reductions/FrontPieces.lean`:

1. `emitConst` writes exactly the constant (incl. a real machine flattening),
   with an OUT-only frame;
2. `reencLoop` appends exactly `encSyms ((· + off)-shifted bits)` for `off = 0`
   (raw symbols, the toy) and `off = 1` (the `shiftReg` cell shift the C8-4
   tape prefix needs), drains its scan register, and leaves `src` intact;
3. `unaryMonomial` writes exactly `1^(c·(n+1)^k + d)` (incl. `k = 0` and
   `c = 0` edges);
4. the `C8SeamProbe` toy front program REBUILT from the real pieces still hits
   the frozen `headEncodeIn` layout register-exactly (`checkBridge` pattern)
   with all emitted cells ∈ {0,1} — the C8-4 assembly shape, validated.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/C8FrontProbe.lean`
-/

open Complexity.Lang FrontPieces

namespace C8FrontProbe

open HeadLayout (encSyms flattenTM headRegBound headEncodeIn)

/-! ## 1. `emitConst` -/

def M0 : FlatTM :=
  { sig := 4, tapes := 1, states := 2,
    trans := [⟨0, [some 3], 1, [some 3], [.Nmove]⟩],
    start := 0, halt := [false, true] }

-- the machine constant lands register-exactly, dirty prior content cleared
#eval (emitConst 1 (encSyms (flattenTM M0))).eval [[1, 0], [9, 9, 9]]
  == [[1, 0], encSyms (flattenTM M0)]                                -- expect true
-- frame: only dst changes
#eval (emitConst 0 [1, 1, 0, 1]).eval [[0], [5], [7]] == [[1, 1, 0, 1], [5], [7]]  -- expect true

/-! ## 2. `reencLoop` — regs: cnt 5, scan 6, tflg 7, src 0, dst 2 -/

def reencAt (off : Nat) (s : State) : State := (reencLoop off 5 6 7 0 2).eval s

-- off = 0: raw symbols; src intact, scan drained, dst appended
#eval reencAt 0 [[1, 0, 1, 1, 0], [8], [9]]
  == [[1, 0, 1, 1, 0], [8], [9] ++ encSyms [1, 0, 1, 1, 0], [], [], [1, 1, 1, 1], [], [0]]
  -- expect true
-- off = 1: the shiftReg cell shift (0 ↦ symbol 1, 1 ↦ symbol 2)
#eval (State.get (reencAt 1 [[1, 0, 1]]) 2)
  == encSyms (Compile.shiftReg [1, 0, 1])                            -- expect true
-- empty input: dst untouched, scan empty
#eval (reencAt 1 [[]]) == [[], [], [], [], [], [], []]               -- expect true

/-! ## 3. `unaryMonomial` — regs: cnt 5, base 6, tmp 7, src 0, dst 3 -/

def monoAt (c k d n : Nat) : List Nat :=
  State.get ((unaryMonomial c k d 5 6 7 0 3).eval [List.replicate n 1]) 3

#eval monoAt 2 2 5 3 == List.replicate (2 * 4 ^ 2 + 5) 1   -- 37 ones; expect true
#eval monoAt 1 2 0 4 == List.replicate 25 1                -- (n+1)²; expect true
#eval monoAt 2 1 1 3 == List.replicate (2 * 3 + 3) 1       -- 2n+3; expect true
#eval monoAt 3 0 2 7 == List.replicate 5 1                 -- k = 0: c + d; expect true
#eval monoAt 0 3 4 2 == List.replicate 4 1                 -- c = 0: d only; expect true
#eval monoAt 2 2 5 0 == List.replicate 7 1                 -- n = 0: c + d; expect true
-- the monomial's frame: src intact, dst exact, scratch (base/tmp/cnt) dirty is OK
#eval ((unaryMonomial 1 2 0 5 6 7 0 4).eval [List.replicate 3 1]).take 4
  == [List.replicate 3 1, [], [], []]                      -- expect true

/-! ## 4. The toy front program of `C8SeamProbe`, rebuilt from the REAL pieces

`fQ n = (M0, 1^n, 2n+3, (n+1)²)` — machine constant via `emitConst`, symbol
stream via `reencLoop` at `off = 0` (the toy's `s` is the raw content), the
two parameters via `unaryMonomial` (`2·(n+1)^1 + 1` and `1·(n+1)^2 + 0`).
Scratch strictly ≥ `headRegBound`: cnt 5, scan 6, tflg 7, base 8, tmp 9. -/

def fQ (n : Nat) : FlatTM × List Nat × Nat × Nat :=
  (M0, List.replicate n 1, 2 * n + 3, (n + 1) * (n + 1))

def buildFront' : Cmd :=
  emitConst 1 (encSyms (flattenTM M0)) ;;
  Cmd.op (.clear 2) ;;
  reencLoop 0 5 6 7 0 2 ;;
  unaryMonomial 2 1 1 5 8 9 0 3 ;;
  unaryMonomial 1 2 0 5 8 9 0 4 ;;
  Cmd.op (.clear 0)

def agreeBelowB (k : Nat) (s t : State) : Bool :=
  (List.range k).all (fun r => State.get s r == State.get t r)

def checkBridge (n : Nat) : Bool :=
  agreeBelowB headRegBound (buildFront'.eval [List.replicate n 1]) (headEncodeIn (fQ n))

def checkBits (n : Nat) : Bool :=
  ((buildFront'.eval [List.replicate n 1]).take headRegBound).all
    (fun reg => reg.all (· < 2))

#eval checkBridge 0   -- expect true
#eval checkBridge 1   -- expect true
#eval checkBridge 2   -- expect true
#eval checkBridge 5   -- expect true
#eval checkBits 0     -- expect true
#eval checkBits 5     -- expect true

-- Summary verdict.
#eval [0, 1, 2, 5].all (fun n => checkBridge n && checkBits n)   -- expect true

end C8FrontProbe
