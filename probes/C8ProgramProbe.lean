import Complexity.NP.SAT.CookLevin.Reductions.FrontProgram

/-! # C8-4 piece 2 probe — the reduction program against `headEncodeIn`

`#eval` validation (probe-before-prove companion to `frontProgram_run`) that
`FrontProgram.frontProgram` emits the four front-instance registers exactly in
the frozen `HeadLayout.headEncodeIn` layout (regs 0–4), for a realistic
multi-register split input plus the **unary size register** (design finding
Option A: `encodeIn x = encX x ++ [1^(size x)]`).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/C8ProgramProbe.lean`
-/

open Complexity.Lang FrontProgram
open HeadLayout (encSyms flattenTM headRegBound headEncodeIn)

namespace C8ProgramProbe

def M0 : FlatTM :=
  { sig := 4, tapes := 1, states := 2,
    trans := [⟨0, [some 3], 1, [some 3], [.Nmove]⟩],
    start := 0, halt := [false, true] }

/-- A toy split input `encX x` of width 2, followed by the size register `1^m`
at index 2. `B = max headRegBound (xWidth+1) = 5`. -/
def inp (encX0 encX1 : List Nat) (m : Nat) : State :=
  [encX0, encX1, List.replicate m 1]

/-- The program: machine `M0`, `xWidth = 2`, `B = 5`, two overshoot monomials
`2·(m+1)^1 + 1` and `1·(m+1)^2 + 0`. -/
def prog : Cmd :=
  frontProgram (encSyms (flattenTM M0)) 2 5 2 1 1 1 2 0

/-- The expected front instance for input `[encX0, encX1, 1^m]`. -/
def expected (encX0 encX1 : List Nat) (m : Nat) : FlatTM × List Nat × Nat × Nat :=
  (M0, 3 :: Compile.encodeRegs [encX0, encX1], 2 * (m + 1) + 1, (m + 1) * (m + 1))

def agreeBelowB (k : Nat) (s t : State) : Bool :=
  (List.range k).all (fun r => State.get s r == State.get t r)

def check (encX0 encX1 : List Nat) (m : Nat) : Bool :=
  agreeBelowB headRegBound
    (prog.eval (inp encX0 encX1 m)) (headEncodeIn (expected encX0 encX1 m))

-- register-exact against headEncodeIn on several split inputs / sizes
#eval check [0] [1, 0] 0        -- expect true
#eval check [0] [1, 0] 3        -- expect true
#eval check [] [] 0             -- expect true
#eval check [1, 1] [0] 5        -- expect true
#eval check [0, 1, 0] [1] 2     -- expect true

-- output cells are all bit-level (regs 0–4)
def checkBits (encX0 encX1 : List Nat) (m : Nat) : Bool :=
  ((prog.eval (inp encX0 encX1 m)).take headRegBound).all (fun reg => reg.all (· < 2))

#eval checkBits [0] [1, 0] 3    -- expect true
#eval checkBits [1, 1] [0] 5    -- expect true

-- Summary verdict.
#eval [(([0], [1,0]), 0), (([0],[1,0]), 3), (([],[]), 0),
       (([1,1],[0]), 5), (([0,1,0],[1]), 2)].all
  (fun ⟨⟨a, b⟩, m⟩ => check a b m && checkBits a b m)   -- expect true

end C8ProgramProbe
