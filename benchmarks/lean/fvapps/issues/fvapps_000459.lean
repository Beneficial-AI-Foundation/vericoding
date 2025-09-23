-- <vc-preamble>
def validate_binary_tree_nodes (n : Nat) (leftChild : List Int) (rightChild : List Int) : Bool :=
  sorry

-- Predicate for valid list input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_list (n : Nat) (lst : List Int) : Bool :=
  sorry

-- Property: Result must be of type Bool
-- </vc-definitions>

-- <vc-theorems>
theorem validate_returns_bool (n : Nat) (leftChild rightChild : List Int) :
  ∃ (b : Bool), validate_binary_tree_nodes n leftChild rightChild = b :=
  sorry

-- Property: If result is True, each node has exactly one parent except root

theorem valid_tree_parent_counts {n : Nat} {leftChild rightChild : List Int} 
  (h : validate_binary_tree_nodes n leftChild rightChild = true) :
  ∃ (parent_count : List Nat),
    parent_count.length = n ∧ 
    (parent_count.filter (· = 1)).length = n - 1 ∧
    (parent_count.filter (· = 0)).length = 1 :=
  sorry

-- Property: Empty trees are only valid for n = 1

theorem empty_tree_validity {n : Nat} 
  (h_left : leftChild = List.replicate n (-1))
  (h_right : rightChild = List.replicate n (-1)) :
  validate_binary_tree_nodes n leftChild rightChild = (n = 1) :=
  sorry

-- Property: Invalid node references result in false

theorem invalid_references {n : Nat} {leftChild rightChild : List Int}
  (h : ¬(is_valid_list n leftChild ∧ is_valid_list n rightChild)) :
  validate_binary_tree_nodes n leftChild rightChild = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_binary_tree_nodes 4 [1, -1, 3, -1] [2, -1, -1, -1]

/-
info: False
-/
-- #guard_msgs in
-- #eval validate_binary_tree_nodes 4 [1, -1, 3, -1] [2, 3, -1, -1]

/-
info: False
-/
-- #guard_msgs in
-- #eval validate_binary_tree_nodes 2 [1, 0] [-1, -1]
-- </vc-theorems>