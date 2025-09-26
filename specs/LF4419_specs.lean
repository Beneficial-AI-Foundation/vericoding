-- <vc-preamble>
def isTree (graph : List (List Nat)) : Bool := sorry 

def isValidAdjacencyMatrix (matrix : List (List Nat)) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dfs (graph : List (List Nat)) (node : Nat) (visited : List Nat) : List Nat := sorry

theorem tree_edge_count 
  (graph : List (List Nat)) : 
  isValidAdjacencyMatrix graph → isTree graph → 
  (List.length (List.join graph)) / 2 = graph.length - 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_connected
  (graph : List (List Nat)) :
  isValidAdjacencyMatrix graph → isTree graph →
  ∀ start, (dfs graph start []).length = graph.length := sorry

theorem valid_matrix_nonempty
  (graph : List (List Nat)) :
  isValidAdjacencyMatrix graph → graph.length > 0 := sorry

theorem valid_matrix_indices
  (graph : List (List Nat)) :
  isValidAdjacencyMatrix graph →
  ∀ row ∈ graph, ∀ x ∈ row, x < graph.length := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval isTree [[1], [0]]

/-
info: False
-/
-- #guard_msgs in
-- #eval isTree [[1, 2], [0, 2], [0, 1]]

/-
info: False
-/
-- #guard_msgs in
-- #eval isTree [[1, 2], [0, 2], [0, 1], []]
-- </vc-theorems>