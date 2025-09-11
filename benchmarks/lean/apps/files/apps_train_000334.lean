-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

def numSquares (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numSquares_bounds (n : Nat) (h : n ≥ 1) : 
  1 ≤ numSquares n ∧ numSquares n ≤ 4 := sorry

theorem numSquares_four_pattern (k m : Nat) (h : 4^k * (8*m + 7) > 0) :
  numSquares (4^k * (8*m + 7)) = 4 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval numSquares 12

/-
info: 2
-/
-- #guard_msgs in
-- #eval numSquares 13

/-
info: 4
-/
-- #guard_msgs in
-- #eval numSquares 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible