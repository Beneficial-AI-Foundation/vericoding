-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_unattractiveness (n : Nat) (markers : List Nat) (edges : List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_unattractiveness_same_marker (marker : Nat) : 
  min_unattractiveness 2 [marker, marker] [[1,2]] = 0 := by
  sorry

theorem min_unattractiveness_different_markers :
  min_unattractiveness 2 [0,2] [[1,2]] = 2 := by
  sorry

theorem min_unattractiveness_simple_tree :
  min_unattractiveness 3 [0,1,1] [[1,2], [1,3]] = 1 := by
  sorry

theorem min_unattractiveness_three_markers :
  min_unattractiveness 3 [0,1,2] [[1,2], [1,3]] = 1 := by
  sorry

theorem min_unattractiveness_all_same :
  min_unattractiveness 4 [2,2,2,2] [[1,2], [1,3], [3,4]] = 0 := by
  sorry

theorem min_unattractiveness_all_ones {n : Nat} (h : n > 0) : 
  min_unattractiveness n (List.replicate n 1) (List.range (n-1) |>.map (λ i => [i+1, i+2])) = 0 := by
  sorry
-- </vc-theorems>