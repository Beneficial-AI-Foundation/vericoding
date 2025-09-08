/-
In universe Earth C-137, Rick discovered a special form of magnetic force between two balls if they are put in his new invented basket. Rick has n empty baskets, the ith basket is at position[i], Morty has m balls and needs to distribute the balls into the baskets such that the minimum magnetic force between any two balls is maximum.
Rick stated that magnetic force between two different balls at positions x and y is |x - y|.
Given the integer array position and the integer m. Return the required force.

Example 1:

Input: position = [1,2,3,4,7], m = 3
Output: 3
Explanation: Distributing the 3 balls into baskets 1, 4 and 7 will make the magnetic force between ball pairs [3, 3, 6]. The minimum magnetic force is 3. We cannot achieve a larger minimum magnetic force than 3.

Example 2:
Input: position = [5,4,3,2,1,1000000000], m = 2
Output: 999999999
Explanation: We can use baskets 1 and 1000000000.

Constraints:

n == position.length
2 <= n <= 10^5
1 <= position[i] <= 10^9
All integers in position are distinct.
2 <= m <= position.length
-/

def max_distance (positions : List Nat) (m : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def can_place_balls (distance : Nat) (sorted_pos : List Nat) (m : Nat) : Bool :=
sorry

theorem max_distance_bounds {positions : List Nat} {m : Nat} 
  (h1 : positions.length ≥ 2)
  (h2 : m ≥ 2)
  (h3 : m ≤ positions.length)
  (h4 : ∀ x ∈ positions, x ≥ 1 ∧ x ≤ 1000000000) :
  let result := max_distance positions m
  result ≥ 0 ∧ 
  result ≤ (positions[positions.length-1]! - positions[0]!) :=
sorry

theorem max_distance_placement {positions : List Nat} {m : Nat}
  (h1 : positions.length ≥ 2)
  (h2 : m ≥ 2)
  (h3 : m ≤ positions.length)
  (h4 : ∀ x ∈ positions, x ≥ 1 ∧ x ≤ 1000000000) :
  let result := max_distance positions m
  can_place_balls result positions m = true :=
sorry

theorem max_distance_maximal {positions : List Nat} {m : Nat}
  (h1 : positions.length ≥ 2)
  (h2 : m ≥ 2)
  (h3 : m ≤ positions.length)
  (h4 : ∀ x ∈ positions, x ≥ 1 ∧ x ≤ 1000000000) :
  let result := max_distance positions m
  result < (positions[positions.length-1]! - positions[0]!) →
  can_place_balls (result + 1) positions m = false :=
sorry

theorem max_distance_input_preservation {positions : List Nat} {m : Nat}
  (h1 : positions.length ≥ 2)
  (h2 : m ≥ 2)
  (h3 : m ≤ positions.length) :
  positions = positions :=
sorry

theorem max_distance_edge_cases :
  max_distance [1, 1000000000] 2 = 999999999 ∧
  max_distance [1,2,3] 3 = 1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_distance [1, 2, 3, 4, 7] 3

/-
info: 999999999
-/
-- #guard_msgs in
-- #eval max_distance [5, 4, 3, 2, 1, 1000000000] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_distance [1, 2, 3, 4, 5, 6] 4

-- Apps difficulty: interview
-- Assurance level: unguarded