-- <vc-preamble>
def widthOfBinaryTree : TreeNode → Nat
  | _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getHeight : TreeNode → Nat
  | TreeNode.nil => 0
  | TreeNode.node _ l r => 1 + Nat.max (getHeight l) (getHeight r)
-- </vc-definitions>

-- <vc-theorems>
theorem width_is_nonnegative (t : TreeNode) :
  widthOfBinaryTree t ≥ 0 := 
  sorry

theorem width_bounded_by_height (t : TreeNode) :
  widthOfBinaryTree t ≤ 2 ^ (getHeight t) :=
  sorry

theorem empty_tree_width :
  widthOfBinaryTree TreeNode.nil = 0 :=
  sorry

theorem single_node_width (v : Int) :
  widthOfBinaryTree (TreeNode.node v TreeNode.nil TreeNode.nil) = 1 :=
  sorry

theorem linear_tree_width (v : Int) :
  let leftTree := TreeNode.node v 
    (TreeNode.node v 
      (TreeNode.node v 
        (TreeNode.node v TreeNode.nil TreeNode.nil) 
        TreeNode.nil)
      TreeNode.nil)
    TreeNode.nil
  let rightTree := TreeNode.node v 
    TreeNode.nil
    (TreeNode.node v 
      TreeNode.nil
      (TreeNode.node v 
        TreeNode.nil
        (TreeNode.node v TreeNode.nil TreeNode.nil)))
  widthOfBinaryTree leftTree = 1 ∧ widthOfBinaryTree rightTree = 1 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval widthOfBinaryTree TreeNode(1)

/-
info: 2
-/
-- #guard_msgs in
-- #eval widthOfBinaryTree TreeNode(1)

/-
info: 2
-/
-- #guard_msgs in
-- #eval widthOfBinaryTree TreeNode(1)
-- </vc-theorems>