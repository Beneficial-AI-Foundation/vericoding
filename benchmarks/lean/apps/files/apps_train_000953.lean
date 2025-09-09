/-
Special Numbers 
Mani has encountered a problem on Special numbers in Bytecode. A number S is called a special number if its digits are in an arithmetic progression modulo 10. He has an array consisting of all numbers from 1 to N and needs your help to find the number of special numbers in the array. He has promised you a significant share of the prize money if he wins the contest :p 
Note:
123,99,802 are special numbers.
146 is not a special number 

-----Input-----

Input consists of 1 integer - the value of N

-----Output-----
Print one integer in the first line - the solution to this problem

-----Constraints-----
- 1 ≤ Number of digits in N ≤ 105

Example

Input

123

Output

102
-/

-- <vc-helpers>
-- </vc-helpers>

def count_special_numbers (n: Nat) : Nat := sorry

theorem under_100_returns_self {n: Nat} (h: n ≥ 1 ∧ n ≤ 99) : 
  count_special_numbers n = n := sorry

theorem three_digit_bounds {n: Nat} (h: n ≥ 100 ∧ n ≤ 999) :
  99 ≤ count_special_numbers n ∧ count_special_numbers n ≤ n := sorry

theorem four_digit_bounds {n: Nat} (h: n ≥ 1000 ∧ n ≤ 9999) :
  189 ≤ count_special_numbers n ∧ count_special_numbers n ≤ n := sorry

theorem output_monotonic {n m: Nat} (h: n ≤ m) :
  count_special_numbers n ≤ count_special_numbers m := sorry

theorem basic_properties {n: Nat} (h: n ≥ 1 ∧ n ≤ 9999) :
  count_special_numbers n ≥ 0 ∧ count_special_numbers n ≤ n := sorry

/-
info: 102
-/
-- #guard_msgs in
-- #eval count_special_numbers 123

/-
info: 99
-/
-- #guard_msgs in
-- #eval count_special_numbers 99

/-
info: 55
-/
-- #guard_msgs in
-- #eval count_special_numbers 55

-- Apps difficulty: interview
-- Assurance level: unguarded