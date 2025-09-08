/-
You are given an array representing a row of seats where seats[i] = 1 represents a person sitting in the ith seat, and seats[i] = 0 represents that the ith seat is empty (0-indexed).
There is at least one empty seat, and at least one person sitting.
Alex wants to sit in the seat such that the distance between him and the closest person to him is maximized. 
Return that maximum distance to the closest person.

Example 1:

Input: seats = [1,0,0,0,1,0,1]
Output: 2
Explanation: 
If Alex sits in the second open seat (i.e. seats[2]), then the closest person has distance 2.
If Alex sits in any other open seat, the closest person has distance 1.
Thus, the maximum distance to the closest person is 2.

Example 2:
Input: seats = [1,0,0,0]
Output: 3
Explanation: 
If Alex sits in the last seat (i.e. seats[3]), the closest person is 3 seats away.
This is the maximum distance possible, so the answer is 3.

Example 3:
Input: seats = [0,1]
Output: 1

Constraints:

2 <= seats.length <= 2 * 104
seats[i] is 0 or 1.
At least one seat is empty.
At least one seat is occupied.
-/

-- <vc-helpers>
-- </vc-helpers>

def max_dist_to_closest : List Nat → Nat := sorry

def List.longestConsecutiveOnes (xs : List Nat) (n : Nat) : Nat := sorry

theorem max_dist_non_negative (seats : List Nat) 
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats ≥ 0 := sorry

theorem max_dist_bounded_by_length (seats : List Nat)
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats ≤ seats.length := sorry

theorem max_dist_gap_bound (seats : List Nat) (i j : Nat)
  (h1 : ∃ x ∈ seats, x = 1)
  (h2 : i < seats.length)
  (h3 : j < seats.length) 
  (h4 : seats.get ⟨i, h2⟩ = 1)
  (h5 : seats.get ⟨j, h3⟩ = 1)
  (h6 : i < j) :
  ((j - i - 1) + 1) / 2 ≤ max_dist_to_closest seats := sorry

theorem max_dist_symmetry (seats : List Nat)
  (h : ∃ x ∈ seats, x = 1) :
  max_dist_to_closest seats = max_dist_to_closest seats.reverse := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_dist_to_closest [1, 0, 0, 0, 1, 0, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_dist_to_closest [1, 0, 0, 0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_dist_to_closest [0, 1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible