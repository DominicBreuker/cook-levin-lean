/-! # `concat` scratch-design probe (bottom-up, 2026-06-27)

Design-level `#eval` validation of the `concat dst src1 src2` gadget plan BEFORE
any proof engineering (HANDOFF bottom-up task 1), at the register/residue
arithmetic level (no real machines — that is `copyAppend`'s job, the one gadget
this design still needs).

`Op.inBounds (concat …)` does NOT force `dst`/`src1`/`src2` distinct, so `dst`
may alias a source. The naive `clear dst ⨾ copy src1 ⨾ copy src2` is then WRONG
(clearing `dst` destroys an aliased source). The aliasing-safe design uses ONE
scratch register `sb` (`> all operands`, empty — provided by the contract):

    opCopy sb src1  ⨾  copyAppend sb src2  ⨾  opCopy dst sb  ⨾  clear sb

**What this probe checks, for every aliasing combination:**
1. output correctness — the 4 stages yield `dst := src1 ++ src2`, scratch restored;
2. the physical RESIDUE the design dumps (each `opCopy`/`clear` frees `|old reg|`
   cells → residue; `copyAppend` is pure growth → 0) against the per-op
   W-invariant budget `cost − sizeGrowth`.

**Result (see table below):** correctness holds for ALL aliasing cases; but the
residue ALWAYS exceeds the original budget `cost = |src1|+|src2|+1` and ALWAYS
fits the BUMPED budget `cost' = 2(|src1|+|src2|)+1` (slack 1). So the scratch
round-trip forces `Op.cost concat` to be bumped to `2(|src1|+|src2|)+1` (faithful:
the round-trip genuinely costs ~2|V| steps; `Op.size_eval_le` keeps holding).

    case            output  residue  allow(bumped)  allow(orig)
    dst∉{s1,s2}      true      6          7              3
    dst=src1         true      5          6              3
    dst=src2         true      7          8              3
    dst=src1=src2    true      6          7              3
    generic distinct true      6          7              2
-/

abbrev St := List (List Nat)
def g (s : St) (i : Nat) : List Nat := s.getD i []
def stt (s : St) (i : Nat) (v : List Nat) : St := s.set i v

-- the 4 stages (opCopy = clear+copy; copyAppend = append, no clear; clear = empty)
def cpy (d sr : Nat) (s : St) : St := stt s d (g s sr)
def app (d sr : Nat) (s : St) : St := stt s d (g s d ++ g s sr)
def clr (d : Nat) (s : St) : St := stt s d []

-- run + accumulate the physical residue each stage dumps (|old content overwritten|)
def concatRun (sb dst src1 src2 : Nat) (s : St) : St × Nat :=
  let s1 := cpy sb src1 s;   let r1 := (g s sb).length
  let s2 := app sb src2 s1;  let r2 := r1
  let s3 := cpy dst sb s2;   let r3 := r2 + (g s2 dst).length
  let s4 := clr sb s3;       let r4 := r3 + (g s3 sb).length
  (s4, r4)

def expected (dst src1 src2 : Nat) (s : St) : St := stt s dst (g s src1 ++ g s src2)
def costBumped (src1 src2 : Nat) (s : St) : Nat := 2*((g s src1).length + (g s src2).length) + 1
def costOrig   (src1 src2 : Nat) (s : St) : Nat := (g s src1).length + (g s src2).length + 1

def check (sb dst src1 src2 : Nat) (s : St) : Bool × Nat × Int × Int :=
  let (out, res) := concatRun sb dst src1 src2 s
  let exp := expected dst src1 src2 s
  let growth : Int := (g exp dst).length - (g s dst).length
  (out == exp, res, (costBumped src1 src2 s : Int) - growth, (costOrig src1 src2 s : Int) - growth)

-- base: reg0=[1,0] reg1=[1,1,1] reg2=[0] reg3=[] (scratch sb=3, empty, > operands {0,1,2})
def base : St := [[1,0], [1,1,1], [0], []]
#eval check 3 0 1 2 base   -- dst∉{src1,src2}
#eval check 3 0 0 2 base   -- dst=src1
#eval check 3 0 1 0 base   -- dst=src2
#eval check 3 0 0 0 base   -- dst=src1=src2
#eval check 3 2 1 0 base   -- generic distinct
