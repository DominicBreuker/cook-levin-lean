/-! # Unary-migration design probe (bottom-up, Risk C2, 2026-06-28)

Design-level `#eval` validation of the **unary migration** (HANDOFF bottom-up
"START HERE") BEFORE any proof engineering (project methodology: probe before
engineering). The migration re-lays the value-as-length trio
(`takeAt`/`dropAt`/`consLen`) and the product encoding **bit-level** so the
compiler's `BitState` invariant (`sig=4`) is preserved.

This probe settles three things at the register-arithmetic level (no real
machines):

1. **The bit-level self-delimiting product encoding round-trips and stays
   `BitState`.** `enc(x,y) = replicate |A| 1 ++ [0] ++ A ++ B` (unary length
   prefix, `0` separator, then the two components). All cells ∈ {0,1}; the `0`
   separator makes the leading 1-run unambiguous even when `A` is empty or `A`
   itself starts with `1`s.

2. **The new trio semantics + the headOnes-based `swap` produce the swapped
   product.** New semantics: `takeAt`/`dropAt` count = the *register's unary
   length* (not the legacy `.headD 0` first-cell value, which is meaningless
   under `BitState`); `consLen dst lenSrc src = replicate |lenSrc| 1 ++ [0] ++ src`
   (writes a unary block, so it now *preserves* `BitState`).

3. **★ KEY FINDING (the handoff's "just re-derive swap" was an under-estimate):
   product unpacking needs a way to recover `L = |A|` from the prefix, which the
   current op set CANNOT do** (`head` peels one cell; `takeAt`/`dropAt` need the
   count they are trying to find — circular). Two routes, BOTH validated below:
     * **Option H** — a new op `headOnes dst src = (src).takeWhile (·==1)`.
     * **Option L (recommended)** — a DSL `forBnd`-loop subroutine
       `extractLeadingOnes` built from EXISTING ops (no new op, no new gadget,
       op count stays 12; correctness is a fold invariant like `EvalCnfCmd`'s
       proven `memberCheck`).

Pure Lean core — no project imports; run with `lean probes/UnaryMigrationProbe.lean`
from the repo root. Expected: every `#eval` prints `true` (then two witness
register dumps). -/

abbrev Reg := List Nat
abbrev St  := List Reg
def get (s : St) (v : Nat) : Reg := (s[v]?).getD []
def set (s : St) (v : Nat) (val : Reg) : St :=
  if v < s.length then List.set s v val
  else (s ++ List.replicate (v + 1 - s.length) []).set v val
def isBit (r : Reg) : Bool := r.all (· ≤ 1)

/-! ## 1. The proposed bit-level product encoding -/

def encProd (A B : Reg) : Reg := List.replicate A.length 1 ++ [0] ++ A ++ B
def decProd (r : Reg) : Reg × Reg :=
  let L := (r.takeWhile (· == 1)).length        -- leading 1-run = |A|
  let rest := (r.drop L).drop 1                 -- skip prefix + the [0] separator
  (rest.take L, rest.drop L)

/-! ## 2. New trio + Option H op semantics -/

def opTakeAt  (s : St) (dst src lenReg : Nat) : St := set s dst ((get s src).take (get s lenReg).length)
def opDropAt  (s : St) (dst src lenReg : Nat) : St := set s dst ((get s src).drop (get s lenReg).length)
def opConsLen (s : St) (dst lenSrc src : Nat) : St :=
  set s dst (List.replicate (get s lenSrc).length 1 ++ [0] ++ get s src)
def opHeadOnes (s : St) (dst src : Nat) : St := set s dst ((get s src).takeWhile (· == 1))  -- Option H
def opTail (s : St) (dst src : Nat) : St := set s dst (get s src).tail
def opConcat (s : St) (dst a b : Nat) : St := set s dst (get s a ++ get s b)

/-- Option-H `swap`: `enc(x,y) ↦ enc(y,x)` (reg0). 7 straight-line ops. -/
def swapProgH (A B : Reg) : St :=
  let s := opHeadOnes [encProd A B] 1 0   -- reg1 := replicate |A| 1   (length |A|)
  let s := opDropAt s 2 0 1               -- reg2 := drop |A| reg0 = [0] ++ A ++ B
  let s := opTail s 2 2                   -- reg2 := A ++ B
  let s := opTakeAt s 3 2 1              -- reg3 := take |A| = A
  let s := opDropAt s 4 2 1              -- reg4 := drop |A| = B
  let s := opConcat s 5 4 3             -- reg5 := B ++ A
  opConsLen s 0 4 5                       -- reg0 := replicate |B| 1 ++ [0] ++ (B ++ A) = enc(y,x)

/-! ## 3b. Option L — extract the prefix with a `forBnd` loop over existing ops -/

inductive Op | clear (d:Nat) | appendOne (d:Nat) | copy (d sr:Nat) | tail (d sr:Nat) | head (d sr:Nat)
inductive Cmd | op (o:Op) | seq (a b:Cmd) | ifBit (t:Nat) (cT cE:Cmd) | forBnd (cnt bnd:Nat) (b:Cmd)
open Op Cmd
def evalOp : Op → St → St
  | Op.clear d, s => set s d [] | Op.appendOne d, s => set s d (get s d ++ [1])
  | Op.copy d sr, s => set s d (get s sr) | Op.tail d sr, s => set s d (get s sr).tail
  | Op.head d sr, s => set s d (match get s sr with | [] => [] | x::_ => [x])
partial def eval : Cmd → St → St
  | Cmd.op o, s => evalOp o s
  | Cmd.seq a b, s => eval b (eval a s)
  | Cmd.ifBit t cT cE, s => if get s t = [1] then eval cT s else eval cE s
  | Cmd.forBnd cnt bnd b, s =>   -- mirrors repo Cmd.run.foldl
      (List.range (get s bnd).length).foldl (fun acc i => eval b (set acc cnt (List.replicate i 1))) s

/-- `dst := leading 1-run of src`, using only EXISTING ops + `forBnd`.
scratch: SC=consumed copy, HD=head holder, DONE=flag, NOOP=no-op sink, CNT=counter. -/
def extractOnes (dst src SC HD DONE NOOP CNT : Nat) : Cmd :=
  Cmd.seq (Cmd.op (Op.copy SC src)) <| Cmd.seq (Cmd.op (Op.clear dst)) <| Cmd.seq (Cmd.op (Op.clear DONE)) <|
  Cmd.forBnd CNT src <|
    Cmd.seq (Cmd.op (Op.head HD SC)) <|
    Cmd.seq (Cmd.ifBit DONE (Cmd.op (Op.clear NOOP))
              (Cmd.ifBit HD (Cmd.op (Op.appendOne dst)) (Cmd.op (Op.appendOne DONE))))
            (Cmd.op (Op.tail SC SC))

/-! ## Test vectors (stressing empty `A` and `1`-leading `A`/`B`) -/

def A1 : Reg := [0,1,0,0,1]
def B1 : Reg := [1,1,0]
def A2 : Reg := []
def B2 : Reg := [1,0,1,1]
def A3 : Reg := [1,1,1]
def B3 : Reg := [1,1,1,0]

-- 1. encoding: bit-level + round-trips (incl. empty A and 1-leading A)
#eval isBit (encProd A1 B1) && isBit (encProd A3 B3)
#eval decProd (encProd A1 B1) == (A1, B1)
#eval decProd (encProd A2 B2) == (A2, B2)
#eval decProd (encProd A3 B3) == (A3, B3)
-- 2. Option-H swap is correct + stays bit-level
#eval get (swapProgH A1 B1) 0 == encProd B1 A1 && isBit (get (swapProgH A1 B1) 0)
#eval get (swapProgH A2 B2) 0 == encProd B2 A2
#eval get (swapProgH A3 B3) 0 == encProd B3 A3
-- 3. Option-L prefix extraction (no new op) is correct, incl. 1-leading data
#eval get (eval (extractOnes 1 0 2 3 4 5 6) [encProd A1 B1]) 1 == List.replicate A1.length 1
#eval get (eval (extractOnes 1 0 2 3 4 5 6) [encProd A2 B2]) 1 == List.replicate A2.length 1
#eval get (eval (extractOnes 1 0 2 3 4 5 6) [encProd A3 B3]) 1 == List.replicate A3.length 1
-- witnesses
#eval encProd A1 B1
#eval get (swapProgH A3 B3) 0
