/-
As you probably know, Fibonacci sequence are the numbers in the following integer sequence:
1, 1, 2, 3, 5, 8, 13...
Write a method that takes the index as an argument and returns last digit from fibonacci number. Example:
  getLastDigit(15) - 610. Your method must return 0 because the last digit of 610 is 0.
Fibonacci sequence grows very fast and value can take very big numbers (bigger than integer type can contain), so, please, be careful with overflow.

[Hardcore version of this kata](http://www.codewars.com/kata/find-last-fibonacci-digit-hardcore-version), no bruteforce will work here ;)
-/

-- <vc-helpers>
-- </vc-helpers>

def get_last_digit (n : Nat) : Nat :=
  sorry

theorem last_digit_in_range (n : Nat) :
  0 ≤ get_last_digit n ∧ get_last_digit n ≤ 9 :=
  sorry

theorem last_digit_periodic (n : Nat) :
  get_last_digit n = get_last_digit (n + 60) :=
  sorry

theorem last_digit_base_cases :
  get_last_digit 0 = 0 ∧ 
  get_last_digit 1 = 1 ∧
  get_last_digit 2 = 1 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_last_digit 15

/-
info: 5
-/
-- #guard_msgs in
-- #eval get_last_digit 193150

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_last_digit 300

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible