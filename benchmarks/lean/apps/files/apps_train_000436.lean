-- <vc-helpers>
-- </vc-helpers>

def find_least_num_unique_ints (arr : List Int) (k : Nat) : Nat :=
  sorry

theorem result_bounds (arr : List Int) (k : Nat) (h : arr ≠ []) :
  0 ≤ find_least_num_unique_ints arr k ∧ 
  find_least_num_unique_ints arr k ≤ arr.length := by
  sorry

theorem removing_all_elements (arr : List Int) (h : arr ≠ []) :
  find_least_num_unique_ints arr arr.length = 0 := by
  sorry

theorem removing_none (arr : List Int) (h : arr ≠ []) :
  find_least_num_unique_ints arr 0 = arr.length := by
  sorry

theorem removing_more_than_length (arr : List Int) (k : Nat) (h : arr ≠ []) :
  find_least_num_unique_ints arr (arr.length + k) = 0 := by
  sorry

theorem monotonic_decrease (arr : List Int) (k : Nat) 
  (h1 : arr.length ≥ 2) (h2 : k ≥ 1) (h3 : k < arr.length) :
  find_least_num_unique_ints arr (k + 1) ≤ find_least_num_unique_ints arr k := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_least_num_unique_ints [5, 5, 4] 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_least_num_unique_ints [4, 3, 1, 1, 3, 3, 2] 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_least_num_unique_ints [2, 4, 1, 8, 3, 5, 1, 3] 3

-- Apps difficulty: interview
-- Assurance level: unguarded