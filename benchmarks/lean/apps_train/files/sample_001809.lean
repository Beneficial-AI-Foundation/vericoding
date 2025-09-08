/-
Given the root of a binary tree, then value v and depth d, you need to add a row of nodes with value v at the given depth d. The root node is at depth 1. 

The adding rule is: given a positive integer depth d, for each NOT null tree nodes N in depth d-1, create two tree nodes with value v as N's left subtree root and right subtree root. And N's original left subtree should be the left subtree of the new left subtree root, its original right subtree should be the right subtree of the new right subtree root. If depth d is 1 that means there is no depth d-1 at all, then create a tree node with value v as the new root of the whole original tree, and the original tree is the new root's left subtree.

Example 1:

Input: 
A binary tree as following:
       4
     /   \
    2     6
   / \   / 
  3   1 5   

v = 1

d = 2

Output: 
       4
      / \
     1   1
    /     \
   2       6
  / \     / 
 3   1   5   

Example 2:

Input: 
A binary tree as following:
      4
     /   
    2    
   / \   
  3   1    

v = 1

d = 3

Output: 
      4
     /   
    2
   / \    
  1   1
 /     \  
3       1

Note:

The given d is in range [1, maximum depth of the given tree + 1].
The given binary tree has at least one tree node.
-/

def list_to_tree : List Int → TreeNode :=
  sorry

def tree_to_list : TreeNode → List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def add_one_row : TreeNode → Int → Int → TreeNode :=
  sorry

theorem add_one_row_result_nonempty (t : TreeNode) (v : Int) (d : Int)
  (h1 : -100 ≤ v ∧ v ≤ 100) (h2 : 1 ≤ d ∧ d ≤ 3) :
  ∃ l : List Int, tree_to_list (add_one_row t v d) = l ∧ l ≠ [] :=
  sorry

theorem add_one_row_depth_one (t : TreeNode) (v : Int) (orig_val : Int)
  (h1 : -100 ≤ v ∧ v ≤ 100) (h2 : t ≠ TreeNode.leaf) :
  let result := add_one_row t v 1
  let result_list := tree_to_list result
  result_list.head? = some v ∧
  result_list.get? 1 = some orig_val :=
  sorry

theorem add_one_row_single_node (val v : Int) (d : Int)
  (h1 : -100 ≤ val ∧ val ≤ 100) (h2 : -100 ≤ v ∧ v ≤ 100) (h3 : d = 1 ∨ d = 2) :
  let t := TreeNode.node val TreeNode.leaf TreeNode.leaf
  let result := add_one_row t v d
  let result_list := tree_to_list result
  (d = 1 → result_list.head? = some v ∧ result_list.get? 1 = some val) ∧
  (d = 2 → result_list.head? = some val ∧ 
           result_list.get? 1 = some v ∧
           result_list.get? 2 = some v) :=
  sorry

/-
info: [4, 1, 1, 2, None, None, 6, 3, 1, 5]
-/
-- #guard_msgs in
-- #eval tree_to_list add_one_row(root1, 1, 2)

/-
info: [4, 2, None, 1, 1, 3, None, None, 1]
-/
-- #guard_msgs in
-- #eval tree_to_list add_one_row(root2, 1, 3)

-- Apps difficulty: interview
-- Assurance level: unguarded