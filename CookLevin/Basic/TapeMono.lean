import CookLevin.Basic.MachineSemantics

/-!
# The tape never shrinks

In this machine model a configuration's tape content is the list `right`; a step replaces
one cell or appends one cell. Consequently the length of `right` is monotone along a run,
and a cell that is never rewritten keeps its value. These facts are used by the tableau
construction and by the compiler's tape invariants.
-/

set_option autoImplicit false

namespace CookLevin

/-- `moveTapeHead` leaves the tape content `right` untouched. -/
theorem moveTapeHead_content (tape : List Nat × Nat × List Nat) (m : TMMove) :
    (moveTapeHead tape m).2.2 = tape.2.2 := by
  cases m <;> rfl

end CookLevin
