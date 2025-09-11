-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_spanning_tree 6 [(1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_spanning_tree 3 []

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_spanning_tree 5 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (1, 3), (2, 4), (3, 5), (4, 1), (5, 2)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded