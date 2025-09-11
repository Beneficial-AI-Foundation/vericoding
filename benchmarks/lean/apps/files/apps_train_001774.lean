-- <vc-preamble>
def Tree (n : Nat) (edges : List (Nat × Nat)) : Prop := sorry 

def sumOfDistancesInTree (n : Nat) (edges : List (Nat × Nat)) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def degree (node : Nat) (edges : List (Nat × Nat)) : Nat := sorry

def isLeafNode (node : Nat) (edges : List (Nat × Nat)) : Prop :=
  degree node edges = 1
-- </vc-definitions>

-- <vc-theorems>
theorem sumOfDistances_output_length 
  (n : Nat) (edges : List (Nat × Nat)) : 
  Tree n edges →
  List.length (sumOfDistancesInTree n edges) = n := 
sorry

theorem sumOfDistances_nonnegative
  (n : Nat) (edges : List (Nat × Nat)) 
  (i : Nat) (h : i < List.length (sumOfDistancesInTree n edges)) :
  Tree n edges →
  List.get! (sumOfDistancesInTree n edges) i ≥ 0 :=
sorry

theorem sumOfDistances_leaf_nodes_max  
  (n : Nat) (edges : List (Nat × Nat)) 
  (node : Nat) (h : node < n) :
  Tree n edges →
  isLeafNode node edges →
  List.get! (sumOfDistancesInTree n edges) node ≤ 
    List.foldr max 0 (sumOfDistancesInTree n edges) :=
sorry

/-
info: [8, 12, 6, 10, 10, 10]
-/
-- #guard_msgs in
-- #eval sum_of_distances_in_tree 6 [[0, 1], [0, 2], [2, 3], [2, 4], [2, 5]]

/-
info: [2, 3, 3]
-/
-- #guard_msgs in
-- #eval sum_of_distances_in_tree 3 [[0, 1], [0, 2]]

/-
info: [6, 4, 4, 6]
-/
-- #guard_msgs in
-- #eval sum_of_distances_in_tree 4 [[0, 1], [1, 2], [2, 3]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded