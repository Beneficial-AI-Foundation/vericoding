-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_path_conditions (N M K : Nat) (roads : List (Nat × Nat)) (Q : Nat) 
  (conditions : List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_path_conditions_result_nonnegative (N M K : Nat) 
  (roads : List (Nat × Nat)) (Q : Nat) (conditions : List (Nat × Nat)) :
  solve_path_conditions N M K roads Q conditions ≥ 0 := sorry

theorem solve_path_conditions_result_bounded (N M K : Nat)
  (roads : List (Nat × Nat)) (Q : Nat) (conditions : List (Nat × Nat)) :
  solve_path_conditions N M K roads Q conditions < 10^9 + 7 := sorry 

theorem single_node_no_conditions (K : Nat) :
  solve_path_conditions 1 0 K [] 0 [] = 1 := sorry

-- Captures test_empty_graph

theorem empty_graph :
  solve_path_conditions 1 0 1 [] 0 [] = 1 := sorry
-- </vc-theorems>