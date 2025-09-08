/-
Given a list of dominoes, dominoes[i] = [a, b] is equivalent to dominoes[j] = [c, d] if and only if either (a==c and b==d), or (a==d and b==c) - that is, one domino can be rotated to be equal to another domino.
Return the number of pairs (i, j) for which 0 <= i < j < dominoes.length, and dominoes[i] is equivalent to dominoes[j].

Example 1:
Input: dominoes = [[1,2],[2,1],[3,4],[5,6]]
Output: 1

Constraints:

1 <= dominoes.length <= 40000
1 <= dominoes[i][j] <= 9
-/

-- <vc-helpers>
-- </vc-helpers>

def numEquivDominoPairs (dominoes : List (List Nat)) : Nat := sorry

theorem output_non_negative 
  (dominoes : List (List Nat)) :
  numEquivDominoPairs dominoes ≥ 0 := sorry

theorem empty_arrays_handled
  (dominoes : List (List Nat)) :
  numEquivDominoPairs (dominoes ++ [[]]) ≥ numEquivDominoPairs dominoes := sorry

theorem identical_pairs_increase_count
  (dominoes : List (List Nat))
  (h : dominoes ≠ [])
  (first : List Nat)
  (h2 : first ∈ dominoes) :
  numEquivDominoPairs (dominoes ++ [first]) ≥ numEquivDominoPairs dominoes := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval numEquivDominoPairs [[1, 2], [2, 1], [3, 4], [5, 6]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval numEquivDominoPairs [[1, 2], [2, 1], [3, 4], [5, 6], [], []]

/-
info: 2
-/
-- #guard_msgs in
-- #eval numEquivDominoPairs [[1, 1], [2, 2], [1, 1], [2, 2]]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible