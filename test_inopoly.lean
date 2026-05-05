import CookLevin.Complexity.Complexity.Definitions

def test_inOPoly : inOPoly (fun n : Nat => n) := by
  unfold inOPoly inO
  exists 1
  exists 0  
  intro n hn
  -- Show: n ≤ 1 * n ^ 1
  simp
  -- The goal should be: n ≤ 1 * n
  -- Which is true because mul_one n = n, so 1 * n = n
  rfl

#check test_inOPoly
