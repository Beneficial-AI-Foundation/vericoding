-- <vc-helpers>
-- </vc-helpers>

def sum_four_divisors (nums: List Nat) : Nat := sorry

theorem sum_four_divisors_nonnegative (nums: List Nat) : 
  sum_four_divisors nums ≥ 0 := sorry

/-
info: 32
-/
-- #guard_msgs in
-- #eval sum_four_divisors [21, 4, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_four_divisors [1, 2, 3, 4]

/-
info: 32
-/
-- #guard_msgs in
-- #eval sum_four_divisors [21]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible