-- <vc-preamble>
def deepest_leaves_sum (root : TreeNode) : Int :=
  sorry

def makeTree (vals : List Int) : TreeNode :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getDeepestLevel (t : TreeNode) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>