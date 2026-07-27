import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp
import Complexity.NP.SAT.CookLevin.Reductions.FrontProgram

/-! # Seam probe — the fourth (S1 → tail) and fifth (C8-5, front → S1) seams

**Top-down session 2026-07-27.** `#eval` validation of the two seams landed in
`Reductions/S1_to_FlatTCC_comp.lean` and `Reductions/Front_to_S1_comp.lean`.

The seam proofs are done, so this probe is not a go/no-go scoping probe; it is
the *risk check* the project's methodology asks for on any new interface —
"does the frame claim hold on real data, not just in the proof I wrote?".
Concretely it pins three things that a future register-frame change would
silently break:

* §1 — `scrub4` erases **exactly** `{0} ∪ [6, 48)`. Its erase set is tied to
  `S1Program.s1RegBound`; if that bound grows, this probe goes red before the
  seam does (the seam would still typecheck against a stale `scrub4` only if
  `s1Program_usesBelow` were also relaxed).
* §2 — `S1Program.s1Key C` really is `FlatTCCFree.encodeIn C`'s registers
  `1`–`5` with register `0` empty. This is the locked invariant that makes the
  fourth seam a pure scrub; it is `rfl` in the proof and *data* here.
* §3 — the **whole C8-5 bridge, end to end, over the full 57-register frame**,
  on the toy front machine of `probes/C8ProgramProbe.lean`. `frontProgram`'s
  own probe only checked agreement below `headRegBound = 5`; this checks that
  `headScrub` really erases everything `W_Q` leaves behind in `[5, 57)`,
  including the extra unary size register the front witness's `encodeIn`
  carries.

Not probed (and not probeable): anything reaching `s1Program`. `#eval` refuses
any expression that reaches a `sorry`, and stage C is still a placeholder —
`probes/S1ProgramProbe.lean` §2 has the numeric check of the S1 contracts
themselves.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/SeamS1Probe.lean`
-/

open Complexity.Lang
open HeadLayout (encSyms flattenTM headRegBound headEncodeIn)

namespace SeamS1Probe

/-! ## §1 — the two scrubs erase exactly their stated ranges -/

/-- A maximally dirty 60-register state: register `r` holds `1^(r+1)`, so no
two registers are equal and "erased" is distinguishable from "copied". -/
def dirty : State := (List.range 60).map (fun r => List.replicate (r + 1) 1)

/-- Which registers `< 60` a scrub leaves empty. -/
def erased (c : Cmd) : List Nat :=
  (List.range 60).filter (fun r => State.get (c.eval dirty) r == [])

/-- Which registers `< 60` a scrub leaves untouched. -/
def kept (c : Cmd) : List Nat :=
  (List.range 60).filter (fun r => State.get (c.eval dirty) r == State.get dirty r)

-- `scrub4` = the fourth seam's `mfc`: register 0 plus the whole S1 scratch
-- block `[6, s1RegBound)`.
#eval erased S1SATComp.scrub4 == 0 :: (List.range' 6 42)          -- expect true
#eval kept S1SATComp.scrub4 == (List.range' 1 5) ++ (List.range' 48 12)  -- expect true

-- the erase set is pinned to `s1RegBound`, not to a magic number
#eval S1Program.s1RegBound == 48                                   -- expect true
#eval (erased S1SATComp.scrub4).getLast? == some (S1Program.s1RegBound - 1)  -- expect true

-- `headScrub` = C8-5's `mfc`: everything from `headRegBound` to the right
-- composite's frame 57.
#eval erased FrontS1Comp.headScrub == List.range' 5 52             -- expect true
#eval kept FrontS1Comp.headScrub == (List.range' 0 5) ++ (List.range' 57 3)  -- expect true
#eval headRegBound == 5                                            -- expect true

-- costs are state-independent constants, well inside the seams' `mfcBound`s
#eval S1SATComp.scrub4.cost dirty                                  -- expect 85 (≤ 100)
#eval FrontS1Comp.headScrub.cost dirty                             -- expect 103 (≤ 110)
#eval S1SATComp.scrub4.cost dirty ≤ 100 && FrontS1Comp.headScrub.cost dirty ≤ 110

/-! ## §2 — `s1Key` IS `FlatTCCFree.encodeIn` on registers 1–5 -/

def sample : List FlatTCC :=
  [ { Sigma := 0, init := [], cards := [], final := [], steps := 0 },
    { Sigma := 3, init := [1, 2, 0], cards := [], final := [[1]], steps := 4 },
    { Sigma := 2, init := [0, 1],
      cards := [⟨⟨0, 1, 0⟩, ⟨1, 0, 1⟩⟩, ⟨⟨1, 1, 1⟩, ⟨0, 0, 0⟩⟩],
      final := [[0, 1], [1]], steps := 7 } ]

/-- The fourth seam's whole premise: the S1 program's output key, laid down at
registers `1`–`5` with register `0` empty, *is* the tail composite's input
state. -/
def keyIsEncodeIn (C : FlatTCC) : Bool :=
  (FlatTCCFree.encodeIn C == [] :: S1Program.s1Key C)
    && ((FlatTCCFree.encodeIn C).length == 6)
    && (State.get (FlatTCCFree.encodeIn C) 0 == [])

#eval sample.all keyIsEncodeIn                                     -- expect true

-- …and reading it back with the program's own extractor is the identity.
#eval sample.all (fun C => S1Program.s1Extract (FlatTCCFree.encodeIn C) == S1Program.s1Key C)

/-! ## §3 — the C8-5 bridge, end to end, on the toy front machine

The machine, input layout and program are `probes/C8ProgramProbe.lean`'s
(`xWidth = 2`, `B = 5`, monomials `2(m+1)+1` and `(m+1)²`), so the two probes
check the same object at two frame widths: that one at `headRegBound = 5`,
this one at the right composite's `57` — i.e. including the scrub. -/

def M0 : FlatTM :=
  { sig := 4, tapes := 1, states := 2,
    trans := [⟨0, [some 3], 1, [some 3], [.Nmove]⟩],
    start := 0, halt := [false, true] }

/-- `encX x` of width 2, then the unary size register `1^m` at index
`xWidth = 2` — note it lands *inside* the head frame and must be overwritten
by the program's output copies, not merely scrubbed. -/
def inp (encX0 encX1 : List Nat) (m : Nat) : State :=
  [encX0, encX1, List.replicate m 1]

def prog : Cmd := FrontProgram.frontProgram (encSyms (flattenTM M0)) 2 5 2 1 1 1 2 0

def expected (encX0 encX1 : List Nat) (m : Nat) : FlatTM × List Nat × Nat × Nat :=
  (M0, 3 :: Compile.encodeRegs [encX0, encX1], 2 * (m + 1) + 1, (m + 1) * (m + 1))

def agreeBelowB (k : Nat) (s t : State) : Bool :=
  (List.range k).all (fun r => State.get s r == State.get t r)

/-- **The C8-5 bridge on the right composite's whole frame.** -/
def checkBridge57 (encX0 encX1 : List Nat) (m : Nat) : Bool :=
  agreeBelowB 57
    (FrontS1Comp.headScrub.eval (prog.eval (inp encX0 encX1 m)))
    (headEncodeIn (expected encX0 encX1 m))

#eval checkBridge57 [0] [1, 0] 0        -- expect true
#eval checkBridge57 [0] [1, 0] 3        -- expect true
#eval checkBridge57 [] [] 0             -- expect true
#eval checkBridge57 [1, 1] [0] 5        -- expect true
#eval checkBridge57 [0, 1, 0] [1] 2     -- expect true

-- Without the scrub the bridge is FALSE at 57 — the probe's evidence that
-- `mfc` is load-bearing here, not cosmetic (the front program parks scratch
-- at `B = 5 … B + 8`, i.e. inside the right frame).
#eval agreeBelowB 57 (prog.eval (inp [0] [1, 0] 3))
        (headEncodeIn (expected [0] [1, 0] 3))                     -- expect FALSE

/-! ## Summary verdict -/

#eval (erased S1SATComp.scrub4 == 0 :: (List.range' 6 42))
    && (kept S1SATComp.scrub4 == (List.range' 1 5) ++ (List.range' 48 12))
    && (erased FrontS1Comp.headScrub == List.range' 5 52)
    && (kept FrontS1Comp.headScrub == (List.range' 0 5) ++ (List.range' 57 3))
    && sample.all keyIsEncodeIn
    && [(([0], [1,0]), 0), (([0],[1,0]), 3), (([],[]), 0),
        (([1,1],[0]), 5), (([0,1,0],[1]), 2)].all
         (fun ⟨⟨a, b⟩, m⟩ => checkBridge57 a b m)                  -- expect true

end SeamS1Probe
