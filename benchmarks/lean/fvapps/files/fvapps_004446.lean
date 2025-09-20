-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>