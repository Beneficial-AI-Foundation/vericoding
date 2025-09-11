-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallest_integer (matrix : List (List Int)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem smallest_integer_result_nonnegative (matrix : List (List Int)) :
  0 ≤ smallest_integer matrix := sorry

theorem smallest_integer_not_in_matrix (matrix : List (List Int)) :
  ¬ (∃ row ∈ matrix, ∃ x ∈ row, x ≥ 0 ∧ x = smallest_integer matrix) := sorry

theorem negative_numbers_ignored (matrix : List (List Int)) :
  smallest_integer matrix = 
  smallest_integer (List.map (λ row => List.map (λ x => if x ≥ 0 then x else -1) row) matrix) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval smallest_integer [[0, 2], [5, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_integer [[1, 2], [3, 4]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_integer [[-1, -1], [-1, -1]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible