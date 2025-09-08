/-
Given the root of a binary tree, consider all root to leaf paths: paths from the root to any leaf.  (A leaf is a node with no children.)
A node is insufficient if every such root to leaf path intersecting this node has sum strictly less than limit.
Delete all insufficient nodes simultaneously, and return the root of the resulting binary tree.

Example 1:

Input: root = [1,2,3,4,-99,-99,7,8,9,-99,-99,12,13,-99,14], limit = 1

Output: [1,2,3,4,null,null,7,8,9,null,14]

Example 2:

Input: root = [5,4,8,11,null,17,4,7,1,null,null,5,3], limit = 22

Output: [5,4,8,11,null,17,4,7,null,null,null,5]

Example 3:

Input: root = [1,2,-3,-5,null,4,null], limit = -1

Output: [1,null,-3,4]

Note:

The given tree will have between 1 and 5000 nodes.
-10^5 <= node.val <= 10^5
-10^9 <= limit <= 10^9
-/

def arrayToTree : List (Option Int) → Option TreeNode := sorry
def treeToArray : Option TreeNode → List (Option Int) := sorry

def sufficientSubset : Option TreeNode → Int → Option TreeNode := sorry
def is_leaf : TreeNode → Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def path_sum : TreeNode → Int := sorry

theorem sufficient_subset_is_subset (tree : List (Option Int)) (limit : Int)
  (h : ∃ n, n ∈ tree ∧ n ≠ none) : 
  let root := arrayToTree tree
  let result := sufficientSubset root limit
  let result_arr := treeToArray result
  ∀ x ∈ result_arr, x ≠ none → x ∈ tree := sorry

theorem sufficient_subset_preserves_root (tree : List (Option Int)) (limit : Int)
  (h₁ : tree.length > 0)
  (h₂ : ∃ x, tree.head? = some (some x)) :
  let root := arrayToTree tree
  let result := sufficientSubset root limit
  let result_arr := treeToArray result
  result_arr.length > 0 → result_arr.head? = tree.head? := sorry

theorem sufficient_subset_leaf_property (tree : List (Option Int)) (limit : Int)
  (h : ∃ n, n ∈ tree ∧ n ≠ none) :
  let root := arrayToTree tree
  let result := sufficientSubset root limit
  match result with
  | none => True
  | some node => is_leaf node → path_sum node ≥ limit := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval treeToArray sufficientSubset(root1, 1)

/-
info: expected2
-/
-- #guard_msgs in
-- #eval treeToArray sufficientSubset(root2, 22)

/-
info: expected3
-/
-- #guard_msgs in
-- #eval treeToArray sufficientSubset(root3, -1)

-- Apps difficulty: interview
-- Assurance level: unguarded