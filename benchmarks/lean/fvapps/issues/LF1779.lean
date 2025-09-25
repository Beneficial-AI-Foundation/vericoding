-- <vc-preamble>
def isValidBST : TreeNode → Bool :=
  sorry

def make_valid_bst : List Int → TreeNode :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insertIntoBST : TreeNode → Int → TreeNode :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_bst_from_sorted_values (values : List Int) :
  isValidBST (make_valid_bst values) = true :=
  sorry

theorem empty_tree_is_valid :
  isValidBST TreeNode.leaf = true :=
  sorry 

theorem single_node_is_valid (value : Int) :
  isValidBST (TreeNode.node value TreeNode.leaf TreeNode.leaf) = true :=
  sorry

theorem bst_remains_valid_after_insert (tree : TreeNode) (value : Int) :
  isValidBST tree = true →
  isValidBST (insertIntoBST tree value) = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval isValidBST TreeNode(2)

/-
info: False
-/
-- #guard_msgs in
-- #eval isValidBST TreeNode(5)

/-
info: True
-/
-- #guard_msgs in
-- #eval isValidBST TreeNode(1)
-- </vc-theorems>