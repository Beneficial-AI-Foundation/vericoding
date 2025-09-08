/-
Given a set of N people (numbered 1, 2, ..., N), we would like to split everyone into two groups of any size.
Each person may dislike some other people, and they should not go into the same group. 
Formally, if dislikes[i] = [a, b], it means it is not allowed to put the people numbered a and b into the same group.
Return true if and only if it is possible to split everyone into two groups in this way.

Example 1:
Input: N = 4, dislikes = [[1,2],[1,3],[2,4]]
Output: true
Explanation: group1 [1,4], group2 [2,3]

Example 2:
Input: N = 3, dislikes = [[1,2],[1,3],[2,3]]
Output: false

Example 3:
Input: N = 5, dislikes = [[1,2],[2,3],[3,4],[4,5],[1,5]]
Output: false

Constraints:

1 <= N <= 2000
0 <= dislikes.length <= 10000
dislikes[i].length == 2
1 <= dislikes[i][j] <= N
dislikes[i][0] < dislikes[i][1]
There does not exist i != j for which dislikes[i] == dislikes[j].
-/

-- <vc-helpers>
-- </vc-helpers>

def possible_bipartition (n : Nat) (dislikes : List (List Nat)) : Bool :=
  sorry

theorem empty_dislikes_always_possible {n : Nat} {dislikes : List (List Nat)} :
  n ≥ 2 → dislikes = [] → possible_bipartition n dislikes = true := by
  sorry

theorem single_pair_always_possible {n : Nat} {dislikes : List (List Nat)} :
  n ≥ 2 → dislikes.length = 1 → possible_bipartition n dislikes = true := by
  sorry

theorem triangle_impossible :
  possible_bipartition 3 [[1,2], [2,3], [1,3]] = false := by
  sorry

theorem simple_chain_possible :
  possible_bipartition 4 [[1,2], [2,3], [3,4]] = true := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval possible_bipartition 4 [[1, 2], [1, 3], [2, 4]]

/-
info: False
-/
-- #guard_msgs in
-- #eval possible_bipartition 3 [[1, 2], [1, 3], [2, 3]]

/-
info: False
-/
-- #guard_msgs in
-- #eval possible_bipartition 5 [[1, 2], [2, 3], [3, 4], [4, 5], [1, 5]]

-- Apps difficulty: interview
-- Assurance level: unguarded