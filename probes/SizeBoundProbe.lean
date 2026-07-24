import Complexity.Simulators.CookTableau
import Complexity.Simulators.GuessTableau

open Complexity Complexity.Simulators

/-- n as in the cook size-bound statement. -/
def nOf (M : FlatTM) (s : List Nat) (steps : Nat) : Nat :=
  s.length + steps + M.sig + M.states + M.trans.length + 2

/-- gn as in the guess size-bound statement (includes maxSize). -/
def gnOf (M : FlatTM) (s : List Nat) (maxSize steps : Nat) : Nat :=
  s.length + maxSize + steps + M.sig + M.states + M.trans.length + 2

def greport (name : String) (M : FlatTM) (s : List Nat) (maxSize steps : Nat) : String :=
  let gn := gnOf M s maxSize steps
  let gsz := encodable.size (guessTableau M s maxSize steps)
  s!"{name}: gn={gn}, guess.size={gsz}, (gn+1)^10 ok={decide (gsz ≤ (gn+1)^10)}, gn^10 ok={decide (gsz ≤ gn^10)}"

def mkEntry (src : Nat) (m : Option Nat) (dst : Nat) (w : Option Nat) (mv : TMMove) :
    FlatTMTransEntry :=
  { src_state := src, src_tape_vals := [m], dst_state := dst,
    dst_write_vals := [w], move_dirs := [mv] }

-- A few small machines of increasing size.
def M0 : FlatTM := { sig := 0, tapes := 1, states := 0, trans := [], start := 0, halt := [] }

def M1 : FlatTM :=
  { sig := 1, tapes := 1, states := 1,
    trans := [mkEntry 0 (some 0) 0 (some 0) TMMove.Rmove],
    start := 0, halt := [false, true] }

def M2 : FlatTM :=
  { sig := 2, tapes := 1, states := 2,
    trans := [mkEntry 0 (some 0) 1 (some 1) TMMove.Rmove,
              mkEntry 1 (some 1) 0 (some 0) TMMove.Lmove,
              mkEntry 0 (some 1) 2 (some 0) TMMove.Nmove],
    start := 0, halt := [false, false, true] }

def M3 : FlatTM :=
  { sig := 3, tapes := 1, states := 3,
    trans := (List.range 4).flatMap (fun q =>
      (List.range 4).map (fun m =>
        mkEntry q (some m) ((q+1) % 4) (some ((m+1) % 4)) TMMove.Rmove)),
    start := 0, halt := [false, false, false, true] }

def report (name : String) (M : FlatTM) (s : List Nat) (steps : Nat) : String :=
  let n := nOf M s steps
  let sz := encodable.size (cookTableau M s steps)
  let gsz := encodable.size (guessTableau M s 0 steps)
  s!"{name}: n={n}, cook.size={sz}, guess.size={gsz}, cook_ok(n^10)={decide (sz ≤ n^10)}, guess_ok((n+1)^10)={decide (gsz ≤ (n+1)^10)}, guess_ok(n^10)={decide (gsz ≤ n^10)}"

#eval report "M0 s=[] steps=0" M0 [] 0
#eval report "M0 s=[] steps=3" M0 [] 3
#eval report "M1 s=[0] steps=2" M1 [0] 2
#eval report "M1 s=[0,0] steps=5" M1 [0, 0] 5
#eval report "M2 s=[0,1] steps=4" M2 [0, 1] 4
#eval report "M2 s=[0,1,0] steps=10" M2 [0, 1, 0] 10
#eval report "M3 s=[0,1,2] steps=6" M3 [0, 1, 2] 6
#eval report "M3 s=[0,1,2,3,0] steps=20" M3 [0, 1, 2, 3, 0] 20

#eval greport "M0 max=0 steps=0" M0 [] 0 0
#eval greport "M0 max=50 steps=0" M0 [] 50 0
#eval greport "M0 max=1000 steps=3" M0 [] 1000 3
#eval greport "M1 max=10 steps=2" M1 [0] 10 2
#eval greport "M3 max=100 steps=6" M3 [0,1,2] 100 6
#eval greport "M3 max=0 steps=6" M3 [0,1,2] 0 6
