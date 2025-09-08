/-
Find sum of all the numbers that are multiples of 10 and are less than or equal to a given number "N". (quotes for clarity and be careful of integer overflow)

-----Input-----
Input will start with an integer T the count of test cases, each case will have an integer N.

-----Output-----
Output each values, on a newline.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤1000000000

-----Example-----
Input:
1
10

Output:
10

-----Explanation-----
Example case 1. Only integer that is multiple 10 that is less than or equal to 10 is 10
-/

-- <vc-helpers>
-- </vc-helpers>

def sum_multiples_of_ten (n : Nat) : Nat := sorry

theorem sum_multiples_non_negative (n : Nat) :
  sum_multiples_of_ten n ≥ 0 := sorry

theorem sum_multiples_divisible_by_ten (n : Nat) :
  sum_multiples_of_ten n % 10 = 0 := sorry 

theorem sum_multiples_upper_bound (n : Nat) :
  sum_multiples_of_ten n ≤ (n * n) / 2 := sorry

theorem sum_multiples_monotonic (n : Nat) :
  n ≥ 10 → sum_multiples_of_ten n ≥ sum_multiples_of_ten (n-1) := sorry

theorem sum_multiples_decimal_bracket (n : Nat) :
  sum_multiples_of_ten n = sum_multiples_of_ten (n - n % 10) := sorry

theorem sum_multiples_edge_cases :
  sum_multiples_of_ten 0 = 0 ∧ sum_multiples_of_ten 9 = 0 := sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval sum_multiples_of_ten 10

/-
info: 30
-/
-- #guard_msgs in
-- #eval sum_multiples_of_ten 20

/-
info: 550
-/
-- #guard_msgs in
-- #eval sum_multiples_of_ten 100

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible