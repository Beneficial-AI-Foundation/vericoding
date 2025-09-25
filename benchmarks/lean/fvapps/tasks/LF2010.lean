-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_spanning_tree (n : Nat) (edges : List (Nat × Nat)) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_spanning_tree_non_negative (n : Nat) (edges : List (Nat × Nat)) :
  min_spanning_tree n edges ≥ 0 :=
  sorry

theorem min_spanning_tree_less_than_vertices (n : Nat) (edges : List (Nat × Nat)) :
  min_spanning_tree n edges < n :=
  sorry

theorem min_spanning_tree_empty_edges (n : Nat) :
  min_spanning_tree n [] = 0 :=
  sorry

theorem min_spanning_tree_complete_graph (n : Nat) (edges : List (Nat × Nat)) :
  (edges.length = n * (n-1) / 2) → min_spanning_tree n edges = n-1 :=
  sorry

theorem min_spanning_tree_small_cases :
  (min_spanning_tree 2 [] = 0) ∧ 
  (min_spanning_tree 3 [(1,2), (2,3)] = 1) :=
  sorry
-- </vc-theorems>