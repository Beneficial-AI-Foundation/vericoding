/-
Given a positive integer num consisting only of digits 6 and 9.
Return the maximum number you can get by changing at most one digit (6 becomes 9, and 9 becomes 6).

Example 1:
Input: num = 9669
Output: 9969
Explanation: 
Changing the first digit results in 6669.
Changing the second digit results in 9969.
Changing the third digit results in 9699.
Changing the fourth digit results in 9666. 
The maximum number is 9969.

Example 2:
Input: num = 9996
Output: 9999
Explanation: Changing the last digit 6 to 9 results in the maximum number.
Example 3:
Input: num = 9999
Output: 9999
Explanation: It is better not to apply any change.

Constraints:

1 <= num <= 10^4
num's digits are 6 or 9.
-/

def countChar (s : String) (c : Char) : Nat :=
  (s.data.filter (· = c)).length

-- <vc-helpers>
-- </vc-helpers>

def maximum69Number (n : Nat) : Nat := sorry

theorem maximum69Number_result_geq_input {n : Nat} (h : n > 0) :
  maximum69Number n ≥ n := sorry

theorem maximum69Number_digit_length_preserved {n : Nat} (h : n > 0) :
  String.length (toString (maximum69Number n)) = String.length (toString n) := sorry

/-
info: 9969
-/
-- #guard_msgs in
-- #eval maximum69Number 9669

/-
info: 9999
-/
-- #guard_msgs in
-- #eval maximum69Number 9996

/-
info: 9999
-/
-- #guard_msgs in
-- #eval maximum69Number 9999

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible