import CookLevin.Lang.CostGrow

set_option autoImplicit false

/-! # The cost checker on programs with a hole

`Cmd.chk` (`Lang/CostGrow.lean`) is a decidable pass over the syntax of a program that
certifies its polynomial cost bound. Running it inside the kernel on a very large program is
expensive, and the reduction program of `Reductions/S1Program.lean` is very large because
its innermost loops are copied syntactically. `CmdH` is a program with a hole; `chk_fill`
expresses the pass on `h.fill k` through the pass on `h` and the values of the pass on `k` at
the masks with which the hole is reached. This lets the certificate for a large program be
assembled from kernel checks on its pieces (`Reductions/S1Witness.lean`). -/

namespace CookLevin.Lang

/-- A command with a hole. -/
inductive CmdH : Type where
  | op (o : Op)
  | seq (a b : CmdH)
  | ifBit (t : Var) (a b : CmdH)
  | forBnd (cnt bnd : Var) (body : CmdH)
  | hole

def CmdH.fill (k : Cmd) : CmdH → Cmd
  | .op o => .op o
  | .seq a b => .seq (a.fill k) (b.fill k)
  | .ifBit t a b => .ifBit t (a.fill k) (b.fill k)
  | .forBnd cnt bnd body => .forBnd cnt bnd (body.fill k)
  | .hole => k

def CmdH.ofCmd : Cmd → CmdH
  | .op o => .op o
  | .seq a b => .seq (ofCmd a) (ofCmd b)
  | .ifBit t a b => .ifBit t (ofCmd a) (ofCmd b)
  | .forBnd cnt bnd body => .forBnd cnt bnd (ofCmd body)

theorem CmdH.fill_ofCmd (k : Cmd) : ∀ c : Cmd, (CmdH.ofCmd c).fill k = c
  | .op o => rfl
  | .seq a b => by simp [CmdH.ofCmd, CmdH.fill, fill_ofCmd k a, fill_ofCmd k b]
  | .ifBit t a b => by simp [CmdH.ofCmd, CmdH.fill, fill_ofCmd k a, fill_ofCmd k b]
  | .forBnd cnt bnd body => by simp [CmdH.ofCmd, CmdH.fill, fill_ofCmd k body]

def CmdH.ngmH (ng : Nat) : CmdH → Nat
  | .op o => Op.ngm o
  | .seq a b => a.ngmH ng ||| b.ngmH ng
  | .ifBit _ a b => a.ngmH ng ||| b.ngmH ng
  | .forBnd cnt _ body => bitOf cnt ||| body.ngmH ng
  | .hole => ng

def CmdH.chkH (f : Nat → Bool × Nat × Nat) (ng : Nat) (C : Nat) : CmdH → Bool × Nat × Nat
  | .op o => ((Op.chk C o).1.isSome, Op.cap C o, (Op.chk C o).2)
  | .seq a b =>
      match CmdH.chkH f ng C a with
      | (ok1, C1, B1) =>
          match CmdH.chkH f ng C1 b with
          | (ok2, C2, B2) => (ok1 && ok2, C2, B1 ||| B2)
  | .ifBit _ a b =>
      match CmdH.chkH f ng C a, CmdH.chkH f ng C b with
      | (ok1, C1, B1), (ok2, C2, B2) => (ok1 && ok2, C1 &&& C2, B1 ||| B2)
  | .forBnd cnt bnd body =>
      if C.testBit bnd then
        match CmdH.chkH f ng (bitOf cnt ||| mdiff C (body.ngmH ng)) body with
        | (ok1, Cb, B) =>
            if ok1 then
              (true, mdiff C (bitOf cnt ||| body.ngmH ng) ||| mdiff C B ||| (C &&& Cb), B)
            else
              match CmdH.chkH f ng (bitOf cnt ||| mdiff C (body.ngmH ng) ||| mdiff C B) body with
              | (ok2, Cb2, _) =>
                  (ok2, mdiff C (bitOf cnt ||| body.ngmH ng) ||| mdiff C B
                    ||| (C &&& Cb &&& Cb2), B)
      else (false, mdiff C (bitOf cnt ||| body.ngmH ng), bitOf cnt ||| body.ngmH ng)
  | .hole => f C

theorem CmdH.ngm_fill (k : Cmd) : ∀ h : CmdH, (h.fill k).ngm = h.ngmH k.ngm
  | .op o => rfl
  | .seq a b => by simp [CmdH.fill, CmdH.ngmH, Cmd.ngm, ngm_fill k a, ngm_fill k b]
  | .ifBit t a b => by simp [CmdH.fill, CmdH.ngmH, Cmd.ngm, ngm_fill k a, ngm_fill k b]
  | .forBnd cnt bnd body => by simp [CmdH.fill, CmdH.ngmH, Cmd.ngm, ngm_fill k body]
  | .hole => rfl

theorem CmdH.chk_fill (k : Cmd) : ∀ (h : CmdH) (C : Nat),
    Cmd.chk C (h.fill k) = h.chkH (fun m => Cmd.chk m k) k.ngm C
  | .op o, C => rfl
  | .seq a b, C => by
      simp only [CmdH.fill, Cmd.chk, CmdH.chkH, chk_fill k a, chk_fill k b]
  | .ifBit t a b, C => by
      simp only [CmdH.fill, Cmd.chk, CmdH.chkH, chk_fill k a, chk_fill k b]
  | .forBnd cnt bnd body, C => by
      simp only [CmdH.fill, Cmd.chk, CmdH.chkH, chk_fill k body, CmdH.ngm_fill]
  | .hole, C => rfl

end CookLevin.Lang
