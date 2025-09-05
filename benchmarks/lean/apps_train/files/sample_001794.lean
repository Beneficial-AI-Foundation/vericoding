Given the root of a binary tree, find the maximum value V for which there exists different nodes A and B where V = |A.val - B.val| and A is an ancestor of B.
(A node A is an ancestor of B if either: any child of A is equal to B, or any child of A is an ancestor of B.)

Example 1:

Input: [8,3,10,1,6,null,14,null,null,4,7,13]
Output: 7
Explanation: 
We have various ancestor-node differences, some of which are given below :
|8 - 3| = 5
|3 - 7| = 4
|8 - 1| = 7
|10 - 13| = 3
Among all possible differences, the maximum value of 7 is obtained by |8 - 1| = 7.

Note:

The number of nodes in the tree is between 2 and 5000.
Each node will have value between 0 and 100000.

def maxAncestorDiff : Option TreeNode → Int
  | none => 0
  | some _ => sorry

partial def getAllValues : Option TreeNode → List Int
  | none => []
  | some (TreeNode.mk v l r) => v :: (getAllValues l ++ getAllValues r)

def listMaximum (l : List Int) : Int :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
