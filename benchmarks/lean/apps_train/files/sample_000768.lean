/-
If Give an integer N . Write a program to obtain the sum of the first and last digits of this number.

-----Input-----

The first line contains an integer T, the total number of test cases. Then follow T lines, each line contains an integer N. 

-----Output-----
For each test case, display the sum of first and last digits of N in a new line.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ N ≤ 1000000

-----Example-----
Input
3 
1234
124894
242323

Output
5
5
5
-/

-- <vc-helpers>
-- </vc-helpers>

def sumFirstLastDigit (n : Nat) : Nat :=
  sorry

theorem sum_first_last_digit_in_range (n : Nat) (h : n > 0) :
  let result := sumFirstLastDigit n
  result ≥ 0 ∧ result ≤ 18
  := sorry

theorem single_digit_sum_is_double (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  sumFirstLastDigit n = n + n
  := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 1234

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 124894

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 242323

-- Apps difficulty: interview
-- Assurance level: guarded