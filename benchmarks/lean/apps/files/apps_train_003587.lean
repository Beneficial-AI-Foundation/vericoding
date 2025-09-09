-- <vc-helpers>
-- </vc-helpers>

def find_smallest_int (arr : List Int) : Int :=
sorry

theorem find_smallest_int_membership 
  (arr : List Int)
  (h : arr ≠ []) :
  find_smallest_int arr ∈ arr :=
sorry

theorem find_smallest_int_is_minimum
  (arr : List Int)
  (h : arr ≠ []) :
  ∀ x ∈ arr, find_smallest_int arr ≤ x :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_smallest_int [34, 15, 88, 2]

/-
info: -345
-/
-- #guard_msgs in
-- #eval find_smallest_int [34, -345, -1, 100]

/-
info: -33
-/
-- #guard_msgs in
-- #eval find_smallest_int [78, 56, -2, 12, 8, -33]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible