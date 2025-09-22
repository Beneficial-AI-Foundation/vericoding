-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def direct_graph (n : Nat) (m : Nat) (edges : List (Nat × Nat)) : List Int := sorry

theorem empty_graph (n : Nat) : 
  direct_graph n 0 [] = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_edges :
  direct_graph 2 1 [(1,2)] = [-1] := sorry

theorem valid_small_graph :
  let result := direct_graph 4 4 [(1,2), (1,3), (2,4), (3,4)]
  List.length result = 4 ∧ 
  (∀ x, x ∈ result → x = 0 ∨ x = 1) := sorry

theorem no_solution_triangle :
  direct_graph 3 3 [(1,2), (2,3), (1,3)] = [-1] := sorry

theorem single_node :
  direct_graph 1 0 [] = [] := sorry

theorem parallel_edges :
  let result := direct_graph 2 2 [(1,2), (1,2)]
  List.length result = 2 ∧
  (∀ x, x ∈ result → x = 0 ∨ x = 1) := sorry
-- </vc-theorems>