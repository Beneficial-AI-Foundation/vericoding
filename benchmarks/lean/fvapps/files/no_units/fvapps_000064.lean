-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_skip_points (n : Nat) (arr : List Nat) : Nat := sorry

theorem min_skip_points_non_negative (n : Nat) (arr : List Nat) :
  min_skip_points n arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_skip_points_bounded_by_ones (n : Nat) (arr : List Nat) :
  min_skip_points n arr ≤ (arr.foldl (· + ·) 0) := sorry

theorem min_skip_points_single_element_case (arr : List Nat) :
  arr.length = 1 → min_skip_points 1 arr = (if arr.head! = 1 then 1 else 0) := sorry

theorem min_skip_points_all_zeros (n : Nat) (arr : List Nat) :
  (arr.foldl (· + ·) 0 = 0) → min_skip_points n arr = 0 := sorry

theorem min_skip_points_edge_cases_single :
  min_skip_points 1 [0] = 0 ∧ 
  min_skip_points 1 [1] = 1 := sorry

theorem min_skip_points_edge_cases_two :
  min_skip_points 2 [0, 0] = 0 ∧
  min_skip_points 2 [1, 0] = 1 := sorry

theorem min_skip_points_edge_case_all_zeros :
  min_skip_points 5 [0, 0, 0, 0, 0] = 0 := sorry
-- </vc-theorems>