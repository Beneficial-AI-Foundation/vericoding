-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cat_coloring (n : Nat) (edges : List (Nat × Nat)) (colors : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_white_node :
  solve_cat_coloring 1 [] "W" = 1 := by sorry

theorem single_black_node :
  solve_cat_coloring 1 [] "B" = 0 := by sorry

theorem five_nodes_mixed :
  solve_cat_coloring 5 [(1,2), (2,3), (2,4), (4,5)] "WBBWW" = 5 := by sorry

theorem six_nodes_mixed :
  solve_cat_coloring 6 [(3,1), (4,5), (2,6), (6,1), (3,4)] "WWBWBB" = 7 := by sorry

theorem three_nodes_mixed_nonneg :
  solve_cat_coloring 3 [(1,2), (2,3)] "WBW" ≥ 0 := by sorry

theorem four_nodes_alternating_nonneg :
  solve_cat_coloring 4 [(1,2), (2,3), (3,4)] "WBWB" ≥ 0 := by sorry
-- </vc-theorems>