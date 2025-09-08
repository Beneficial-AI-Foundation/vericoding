/-
The Hamming distance between two integers is the number of positions at which the corresponding bits are different.

Given two integers x and y, calculate the Hamming distance.

Note:
0 ≤ x, y < 231.

Example:

Input: x = 1, y = 4

Output: 2

Explanation:
1   (0 0 0 1)
4   (0 1 0 0)
       ↑   ↑

The above arrows point to positions where the corresponding bits are different.
-/

def hammingDistance (x y : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def bitLength (n : Nat) : Nat :=
  sorry

theorem hamming_distance_symmetry (x y : Nat) :
  hammingDistance x y = hammingDistance y x :=
sorry

theorem hamming_distance_self (x : Nat) :
  hammingDistance x x = 0 :=
sorry

theorem hamming_distance_nonnegative (x y : Nat) :
  hammingDistance x y ≥ 0 :=
sorry

theorem hamming_distance_upper_bound (x y : Nat) :
  hammingDistance x y ≤ max (bitLength x) (bitLength y) :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval hamming_distance 1 4

/-
info: 1
-/
-- #guard_msgs in
-- #eval hamming_distance 3 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval hamming_distance 0 7

-- Apps difficulty: introductory
-- Assurance level: unguarded