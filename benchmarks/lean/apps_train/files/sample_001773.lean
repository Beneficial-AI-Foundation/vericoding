/-
Given a binary tree, return the level order traversal of its nodes' values. (ie, from left to right, level by level).

For example:
Given binary tree [3,9,20,null,null,15,7],

    3
   / \
  9  20
    /  \
   15   7

return its level order traversal as:

[
  [3],
  [9,20],
  [15,7]
]
-/

-- <vc-helpers>
-- </vc-helpers>

def level_order (root : Option TreeNode) : List (List Int) :=
  sorry

theorem level_order_of_none :
  level_order none = [] := by sorry

theorem level_order_single_node (value : Int) :
  level_order (some (TreeNode.mk value none none)) = [[value]] := by sorry

theorem level_order_two_nodes (root_val left_val : Int) :
  level_order (some (TreeNode.mk root_val (some (TreeNode.mk left_val none none)) none)) = [[root_val], [left_val]] := by sorry

theorem level_order_level_sizes {root : Option TreeNode} {result : List (List Int)}
  (h : level_order root = result) :
  ∀ (i : Nat) (level : List Int),
  level ∈ result →
  level.length ≤ 2^i := by sorry

theorem level_order_nonempty_levels {root : Option TreeNode} :
  ∀ level ∈ level_order root,
  level ≠ [] := by sorry

theorem level_order_output_structure {root : Option TreeNode} :
  ∀ level ∈ level_order root,
  level.all (fun _ => true) := by sorry

/-
info: [[3], [9, 20], [15, 7]]
-/
-- #guard_msgs in
-- #eval level_order TreeNode(3)

/-
info: [[1]]
-/
-- #guard_msgs in
-- #eval level_order TreeNode(1)

/-
info: []
-/
-- #guard_msgs in
-- #eval level_order None

-- Apps difficulty: interview
-- Assurance level: unguarded