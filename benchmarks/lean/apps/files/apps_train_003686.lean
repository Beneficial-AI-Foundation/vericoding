-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_by_value_and_index (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_value_and_index_preserves_elements {arr : List Int} (h : arr ≠ []) :
  List.Perm (sort_by_value_and_index arr) arr :=
sorry

theorem sort_by_value_and_index_length {arr : List Int} (h : arr ≠ []) :
  (sort_by_value_and_index arr).length = arr.length :=
sorry

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval sort_by_value_and_index [1, 2, 3, 4, 5]

/-
info: [2, 3, 4, 23, 5]
-/
-- #guard_msgs in
-- #eval sort_by_value_and_index [23, 2, 3, 4, 5]

/-
info: [1, 9, 5, 3, 4]
-/
-- #guard_msgs in
-- #eval sort_by_value_and_index [9, 5, 1, 4, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible