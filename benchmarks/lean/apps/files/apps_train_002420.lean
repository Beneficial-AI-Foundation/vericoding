-- <vc-helpers>
-- </vc-helpers>

def count_largest_group (n : Nat) : Nat := sorry

theorem count_largest_group_positive (n : Nat) (h : n > 0) :
  count_largest_group n > 0 := sorry

theorem count_largest_group_bounded (n : Nat) (h : n > 0) :
  count_largest_group n ≤ n := sorry

theorem count_largest_group_consecutive (n : Nat) (h : n > 0) :
  (count_largest_group n - count_largest_group (n + 1) ≤ n) ∧ 
  (count_largest_group (n + 1) - count_largest_group n ≤ n) := sorry

theorem count_largest_group_edge_cases :
  (count_largest_group 1 = 1) ∧ (count_largest_group 9 = 9) := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_largest_group 13

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_largest_group 2

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_largest_group 15

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible