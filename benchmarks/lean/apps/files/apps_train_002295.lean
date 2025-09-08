/-
Given an integer number n, return the difference between the product of its digits and the sum of its digits.

Example 1:
Input: n = 234
Output: 15 
Explanation: 
Product of digits = 2 * 3 * 4 = 24 
Sum of digits = 2 + 3 + 4 = 9 
Result = 24 - 9 = 15

Example 2:
Input: n = 4421
Output: 21
Explanation: 
Product of digits = 4 * 4 * 2 * 1 = 32 
Sum of digits = 4 + 4 + 2 + 1 = 11 
Result = 32 - 11 = 21

Constraints:

1 <= n <= 10^5
-/

def subtract_product_and_sum (n : Nat) : Int := sorry

def digits (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def product_of_list (l : List Nat) : Nat := sorry

def sum_of_list (l : List Nat) : Nat := sorry

theorem single_digit_zero (n : Nat) (h : n > 0 ∧ n < 10) :
  subtract_product_and_sum n = 0 := sorry

theorem three_digit_bounds (n : Nat) (h : n ≥ 100 ∧ n ≤ 999) :
  subtract_product_and_sum n ≤ 729 ∧ subtract_product_and_sum n ≥ -27 := sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 234

/-
info: 21
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 4421

/-
info: -2
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 111

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible