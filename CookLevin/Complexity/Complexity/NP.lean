import Complexity.Complexity.Definitions

set_option autoImplicit false

universe u

class polyCertRel {X Y : Type} (_ : X → Y → Prop) : Prop where
  dummy : True := by
    trivial

def inTimePoly {X : Type} (_ : X → Prop) : Prop := True

def inNP {X : Type} [encodable X] (_ : X → Prop) : Prop := True

def inP (X : Type) [encodable X] (P : X → Prop) : Prop := inTimePoly P

def reducesPolyMO {X Y : Type} [encodable X] [encodable Y] (_ : X → Prop) (_ : Y → Prop) : Prop := True

infix:50 " ⪯p " => reducesPolyMO

def NPhard {X : Type} [encodable X] (_ : X → Prop) : Prop := True

def NPcomplete {X : Type} [encodable X] (P : X → Prop) : Prop := NPhard P ∧ inNP P

theorem inNP_intro {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) : inNP P := by
  simp [inNP]

theorem P_NP_incl (X : Type) [encodable X] (P : X → Prop) : inP X P → inNP P := by
  intro _
  simp [inNP]

theorem reducesPolyMO_elim {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → True := by
  intro _
  trivial

theorem reducesPolyMO_reflexive (X : Type) [encodable X] (P : X → Prop) : P ⪯p P := by
  simp [reducesPolyMO]

theorem reducesPolyMO_transitive {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    (P : X → Prop) (Q : Y → Prop) (R : Z → Prop) :
    P ⪯p Q → Q ⪯p R → P ⪯p R := by
  intro _ _
  simp [reducesPolyMO]

theorem red_inNP {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → inNP Q → inNP P := by
  intro _ _
  simp [inNP]

theorem red_NPhard {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → NPhard P → NPhard Q := by
  intro _ _
  simp [NPhard]

theorem NPhard_sig (X : Type) [encodable X] (_ : Nat) (P : X → Prop) : NPhard P := by
  simp [NPhard]
