-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Int := sorry

theorem solve_non_negative_or_minus_one (n : Nat) : 
  solve n ≥ -1 := sorry

theorem solve_impossible_single_digit (n : Nat) :
  n < 10 ∧ n % 5 ≠ 0 → solve n = -1 := sorry

theorem solve_leading_zeros (n m : Nat) :
  n = m → solve n = solve m := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve 50

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve 521

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve 7

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible