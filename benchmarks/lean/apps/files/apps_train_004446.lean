-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List (List Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_positive_only {nums : List (List Int)}
  (h : ∀ l ∈ nums, ∀ x ∈ l, 0 ≤ x ∧ x ≤ 100) :
  solve nums = (nums.map (List.foldl max 0)).foldl (· * ·) 1 :=
sorry

theorem solve_unit_arrays {nums : List (List Int)}
  (h : ∀ l ∈ nums, l = [1]) :
  solve nums = 1 :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve [[1, 2], [3, 4]]

/-
info: 45
-/
-- #guard_msgs in
-- #eval solve [[10, -15], [-1, -3]]

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve [[-1, 2, -3, 4], [1, -2, 3, -4]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded