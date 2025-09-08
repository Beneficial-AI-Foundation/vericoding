/-
Given an array arr of positive integers, consider all binary trees such that:

Each node has either 0 or 2 children;
The values of arr correspond to the values of each leaf in an in-order traversal of the tree.  (Recall that a node is a leaf if and only if it has 0 children.)
The value of each non-leaf node is equal to the product of the largest leaf value in its left and right subtree respectively.

Among all possible binary trees considered, return the smallest possible sum of the values of each non-leaf node.  It is guaranteed this sum fits into a 32-bit integer.

Example 1:
Input: arr = [6,2,4]
Output: 32
Explanation:
There are two possible trees.  The first has non-leaf node sum 36, and the second has non-leaf node sum 32.

    24            24
   /  \          /  \
  12   4        6    8
 /  \               / \
6    2             2   4

Constraints:

2 <= arr.length <= 40
1 <= arr[i] <= 15
It is guaranteed that the answer fits into a 32-bit signed integer (ie. it is less than 2^31).
-/

-- <vc-helpers>
-- </vc-helpers>

def mct_from_leaf_values (arr : List Int) : Int :=
  sorry

theorem base_cases :
  mct_from_leaf_values [] = 0 ∧
  mct_from_leaf_values [5] = 0 ∧ 
  mct_from_leaf_values [4, 11] = 44 :=
  sorry

/-
info: 32
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [6, 2, 4]

/-
info: 44
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [4, 11]

/-
info: 500
-/
-- #guard_msgs in
-- #eval mct_from_leaf_values [15, 13, 5, 3, 15]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible