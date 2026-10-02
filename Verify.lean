import CookLevin

/-!
# Checking the result with Lean's own commands

Run `lake env lean Verify.lean` after `lake build`. Everything below uses only built-in
Lean commands, independent of the checks this repository adds to its build.
-/

-- The statement of the main theorem.
#check @CookLevin.cook_levin

-- The definitions it is stated with (see `GUIDE.md` for all of them).
#print CookLevin.NPcomplete
#print CookLevin.NPhard
#print CookLevin.inNP
#print CookLevin.reducesPoly

-- The axioms the proof depends on. Expected: `[propext, Classical.choice, Quot.sound]`,
-- Lean's three standard axioms. A `sorry` anywhere in the proof would appear here as
-- `sorryAx`.
#print axioms CookLevin.cook_levin
