/-
Given a binary tree with the following rules:

root.val == 0
If treeNode.val == x and treeNode.left != null, then treeNode.left.val == 2 * x + 1
If treeNode.val == x and treeNode.right != null, then treeNode.right.val == 2 * x + 2

Now the binary tree is contaminated, which means all treeNode.val have been changed to -1.
You need to first recover the binary tree and then implement the FindElements class:

FindElements(TreeNode* root) Initializes the object with a contamined binary tree, you need to recover it first.
bool find(int target) Return if the target value exists in the recovered binary tree.

Example 1:

Input
["FindElements","find","find"]
[[[-1,null,-1]],[1],[2]]
Output
[null,false,true]
Explanation
FindElements findElements = new FindElements([-1,null,-1]); 
findElements.find(1); // return False 
findElements.find(2); // return True 
Example 2:

Input
["FindElements","find","find","find"]
[[[-1,-1,-1,-1,-1]],[1],[3],[5]]
Output
[null,true,true,false]
Explanation
FindElements findElements = new FindElements([-1,-1,-1,-1,-1]);
findElements.find(1); // return True
findElements.find(3); // return True
findElements.find(5); // return False
Example 3:

Input
["FindElements","find","find","find","find"]
[[[-1,null,-1,-1,null,-1]],[2],[3],[4],[5]]
Output
[null,true,false,false,true]
Explanation
FindElements findElements = new FindElements([-1,null,-1,-1,null,-1]);
findElements.find(2); // return True
findElements.find(3); // return False
findElements.find(4); // return False
findElements.find(5); // return True

Constraints:

TreeNode.val == -1
The height of the binary tree is less than or equal to 20
The total number of nodes is between [1, 10^4]
Total calls of find() is between [1, 10^4]
0 <= target <= 10^6
-/

def make_tree (values : List Int) (max_depth : Nat := 4) : TreeNode := sorry

def initFindElements (root : TreeNode) : FindElements := {
  root := root,
  find := fun _ => false
}

-- <vc-helpers>
-- </vc-helpers>

def isNode : TreeNode → Prop
  | TreeNode.node _ _ _ => True
  | _ => False

theorem initialization_valid {values : List Int} 
  (h : values.length > 0) (h2 : values.length ≤ 15) :
  let root := make_tree values
  ∃ fe : FindElements, True := sorry

theorem empty_tree_find {target : Int}
  (h : target ≥ 0) (h2 : target ≤ 100) :
  let fe := initFindElements TreeNode.nil
  fe.find target = false := sorry

theorem negative_values_not_found {target : Int}
  (h : target < 0) (h2 : target ≥ -100) :
  let root := make_tree [-1, -1, -1, -1]
  let fe := initFindElements root
  fe.find target = false := sorry

theorem valid_indices_found {values : List Int}
  (h : values.length > 0) (h2 : values.length ≤ 15) :
  let root := make_tree values
  let fe := initFindElements root
  fe.find 0 = true ∧ 
  (isNode root → fe.find 2 = true) ∧
  (isNode root → fe.find 1 = true) := sorry

-- Apps difficulty: interview
-- Assurance level: unguarded