-- <vc-helpers>
-- </vc-helpers>

def find_smallest_range (lists : List (List Int)) : Int × Int :=
  sorry

theorem range_contains_number_from_each_list (lists : List (List Int))
    (h1 : ∀ l ∈ lists, l.length > 0) :
  let result := find_smallest_range lists
  ∀ l ∈ lists, ∃ x ∈ l, result.1 ≤ x ∧ x ≤ result.2 := by
  sorry

theorem range_bounds (lists : List (List Int)) 
    (h1 : ∀ l ∈ lists, l.length > 0)
    (h2 : lists.length > 0) :
  let result := find_smallest_range lists
  (∃ l ∈ lists, ∃ x ∈ l, x = result.1) ∧
  (∃ l ∈ lists, ∃ x ∈ l, x = result.2) := by
  sorry

/-
info: [20, 24]
-/
-- #guard_msgs in
-- #eval find_smallest_range [[4, 10, 15, 24, 26], [0, 9, 12, 20], [5, 18, 22, 30]]

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval find_smallest_range [[1, 2, 3], [1, 2, 3], [1, 2, 3]]

/-
info: [10, 11]
-/
-- #guard_msgs in
-- #eval find_smallest_range [[10, 10], [11, 11]]

-- Apps difficulty: interview
-- Assurance level: unguarded