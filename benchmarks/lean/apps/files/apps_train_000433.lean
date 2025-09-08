/-
There are n soldiers standing in a line. Each soldier is assigned a unique rating value.
You have to form a team of 3 soldiers amongst them under the following rules:

Choose 3 soldiers with index (i, j, k) with rating (rating[i], rating[j], rating[k]).
A team is valid if:  (rating[i] < rating[j] < rating[k]) or (rating[i] > rating[j] > rating[k]) where (0 <= i < j < k < n).

Return the number of teams you can form given the conditions. (soldiers can be part of multiple teams).

Example 1:
Input: rating = [2,5,3,4,1]
Output: 3
Explanation: We can form three teams given the conditions. (2,3,4), (5,4,1), (5,3,1). 

Example 2:
Input: rating = [2,1,3]
Output: 0
Explanation: We can't form any team given the conditions.

Example 3:
Input: rating = [1,2,3,4]
Output: 4

Constraints:

n == rating.length
1 <= n <= 200
1 <= rating[i] <= 10^5
-/

-- <vc-helpers>
-- </vc-helpers>

def num_teams (rating : List Int) : Nat :=
  sorry

theorem num_teams_non_negative (rating : List Int) : 
  num_teams rating ≥ 0 := by sorry

theorem num_teams_short_list {rating : List Int} (h : rating.length < 3) : 
  num_teams rating = 0 := by sorry 

theorem num_teams_symmetric {rating : List Int} (h : rating.length ≥ 3) :
  num_teams rating = num_teams rating.reverse := by sorry

theorem num_teams_strictly_monotone {rating : List Int} (h₁ : rating.length ≥ 3) :
  (∀ i, i < rating.length - 1 → rating[i]! < rating[i+1]!) ∨ 
  (∀ i, i < rating.length - 1 → rating[i]! > rating[i+1]!) →
  num_teams rating = (rating.length * (rating.length - 1) * (rating.length - 2)) / 6 := by sorry

theorem num_teams_all_equal {rating : List Int} (h : rating.length ≥ 3) :
  (∀ x ∈ rating, x = rating[0]!) → 
  num_teams rating = 0 := by sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_teams [2, 5, 3, 4, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_teams [2, 1, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval num_teams [1, 2, 3, 4]

-- Apps difficulty: interview
-- Assurance level: unguarded