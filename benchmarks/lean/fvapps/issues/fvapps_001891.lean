-- <vc-preamble>
def postorder_traversal {α : Type} (t : Tree α) : List α := sorry

def build_tree {α : Type} (vals : List α) : Tree α := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_postorder {α : Type} (t : Tree α) : List α := sorry

theorem empty_tree_postorder {α : Type} :
  postorder_traversal (Tree.leaf : Tree α) = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem postorder_matches_expected {α : Type} (vals : List α) :
  vals ≠ [] →
  let tree := build_tree vals
  postorder_traversal tree = get_postorder tree := sorry

theorem single_node_postorder {α : Type} (v : α) :
  postorder_traversal (Tree.node v Tree.leaf Tree.leaf) = [v] := sorry

theorem two_nodes_left_postorder {α : Type} (v1 v2 : α) :
  postorder_traversal (Tree.node v1 (Tree.node v2 Tree.leaf Tree.leaf) Tree.leaf) = [v2, v1] := sorry

theorem two_nodes_right_postorder {α : Type} (v1 v2 : α) :
  postorder_traversal (Tree.node v1 Tree.leaf (Tree.node v2 Tree.leaf Tree.leaf)) = [v2, v1] := sorry

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval postorder_traversal TreeNode(1)

/-
info: [2, 3, 1]
-/
-- #guard_msgs in
-- #eval postorder_traversal TreeNode(1)

/-
info: []
-/
-- #guard_msgs in
-- #eval postorder_traversal None
-- </vc-theorems>