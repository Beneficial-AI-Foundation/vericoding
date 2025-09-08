/-
Given a number N, return a string consisting of "0"s and "1"s that represents its value in base -2 (negative two).
The returned string must have no leading zeroes, unless the string is "0".

Example 1:
Input: 2
Output: "110"
Explantion: (-2) ^ 2 + (-2) ^ 1 = 2

Example 2:
Input: 3
Output: "111"
Explantion: (-2) ^ 2 + (-2) ^ 1 + (-2) ^ 0 = 3

Example 3:
Input: 4
Output: "100"
Explantion: (-2) ^ 2 = 4

Note:

0 <= N <= 10^9
-/

-- <vc-helpers>
-- </vc-helpers>

def base_neg2 (n : Int) : String := sorry

def binaryStringToNegBase2 (s : String) : Int := sorry

theorem base_neg2_valid_binary (n : Int) :
  let s := base_neg2 n
  ∀ c ∈ s.data, c = '0' ∨ c = '1' := sorry

theorem base_neg2_roundtrip (n : Int) : 
  binaryStringToNegBase2 (base_neg2 n) = n := sorry

theorem base_neg2_positive (n : Int) :
  n ≥ 0 →
  (base_neg2 n).length > 0 ∧ 
  (base_neg2 n).data.head? ≠ some '-' := sorry

theorem base_neg2_zero :
  base_neg2 0 = "0" := sorry

theorem base_neg2_length (n : Int) (h : n > 0) :
  let binary_length := String.length (base_neg2 n)
  binary_length ≤ String.length (toString n) + 2 := sorry

/-
info: '110'
-/
-- #guard_msgs in
-- #eval base_neg2 2

/-
info: '111'
-/
-- #guard_msgs in
-- #eval base_neg2 3

/-
info: '100'
-/
-- #guard_msgs in
-- #eval base_neg2 4

-- Apps difficulty: interview
-- Assurance level: unguarded