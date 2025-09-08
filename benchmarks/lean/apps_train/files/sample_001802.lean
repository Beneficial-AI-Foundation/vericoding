/-
Given a binary tree, return the sum of values of its deepest leaves.

Example 1:

Input: root = [1,2,3,4,5,null,6,7,null,null,null,null,8]
Output: 15

Constraints:

The number of nodes in the tree is between 1 and 10^4.
The value of nodes is between 1 and 100.
-/

def deepest_leaves_sum (root : TreeNode) : Int :=
  sorry

def makeTree (vals : List Int) : TreeNode :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def getDeepestLevel (t : TreeNode) : List Int :=
  sorry

theorem single_path_tree_deepest_sum {vals : List Int} (h : vals ≠ []) :
  let v := vals.head!
  let root := TreeNode.mk v none none
  let path := vals.tail.foldl (fun acc v => 
    TreeNode.mk v (some acc) none) root
  deepest_leaves_sum path = vals.getLast! 
  := sorry

theorem level_order_tree_deepest_sum {vals : List Int} (h : vals ≠ []) : 
  let v := vals.head!
  let root := TreeNode.mk v none none
  deepest_leaves_sum root = (getDeepestLevel (makeTree vals)).foldl (· + ·) 0
  := sorry

theorem single_node_deepest_sum (v : Int) :
  deepest_leaves_sum (TreeNode.mk v none none) = v
  := sorry

theorem two_level_tree_deepest_sum :
  let root := TreeNode.mk 1 
    (some (TreeNode.mk 2 none none))
    (some (TreeNode.mk 3 none none))
  deepest_leaves_sum root = 5
  := sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval deepest_leaves_sum TreeNode(1)

/-
info: 1
-/
-- #guard_msgs in
-- #eval deepest_leaves_sum TreeNode(1)

/-
info: 5
-/
-- #guard_msgs in
-- #eval deepest_leaves_sum TreeNode(1)

-- Apps difficulty: interview
-- Assurance level: unguarded