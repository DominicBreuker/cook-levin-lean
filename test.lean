import Complexity.Complexity.Definitions

example : inOPoly (fun n => n) := by
  unfold inOPoly inO
  use 1
  use 0
  intro n hn
  sorry
