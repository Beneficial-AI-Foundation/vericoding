def max_non_overlapping (nums: List Int) (target: Int) : Nat :=
  sorry

def abs (n: Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_list (l: List Nat) : Nat :=
  sorry

theorem max_non_overlapping_non_negative (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≥ 0 :=
sorry

theorem max_non_overlapping_bounded_by_length (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≤ nums.length :=
sorry

theorem max_non_overlapping_empty_list (target: Int) :
  max_non_overlapping [] target = 0 :=
sorry

theorem max_non_overlapping_all_zeros (n: Nat) :
  max_non_overlapping (List.replicate n 0) 0 = n :=
sorry

theorem max_non_overlapping_self_consistent (nums: List Int) (target: Int) :
  max_non_overlapping nums target = max_non_overlapping nums target :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_non_overlapping [1, 1, 1, 1, 1] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_non_overlapping [-1, 3, 5, 1, 4, 2, -9] 6

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_non_overlapping [0, 0, 0] 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible