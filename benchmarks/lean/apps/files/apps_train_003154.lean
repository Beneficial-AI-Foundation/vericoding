/-
# Task
 Two integer numbers are added using the column addition method. When using this method, some additions of digits produce non-zero carries to the next positions. Your task is to calculate the number of non-zero carries that will occur while adding the given numbers.

 The numbers are added in base 10.

# Example

 For `a = 543 and b = 3456,` the output should be `0`

 For `a = 1927 and b = 6426`, the output should be `2`

 For `a = 9999 and b = 1`, the output should be `4`

# Input/Output

 - `[input]` integer `a`

  A positive integer.

  Constraints: `1 ≤ a ≤ 10^7`

 - `[input]` integer `b`

  A positive integer.

  Constraints: `1 ≤ b ≤ 10^7`

 - `[output]` an integer
-/

-- <vc-helpers>
-- </vc-helpers>

def number_of_carries (a b : Nat) : Nat := sorry

theorem carries_non_negative (a b : Nat) : 
  number_of_carries a b ≥ 0 := sorry

theorem carries_max_digits (a b : Nat) :
  number_of_carries a b ≤ String.length (toString (max a b)) := sorry

theorem carries_with_zero (x : Nat) :
  number_of_carries x 0 = 0 ∧ number_of_carries 0 x = 0 := sorry

theorem single_digit_no_carry {d1 d2 : Nat} :
  d1 ≤ 9 → d2 ≤ 9 → d1 + d2 < 10 → 
  number_of_carries d1 d2 = 0 := sorry

theorem identical_numbers (x : Nat) :
  number_of_carries x x = number_of_carries x x := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval number_of_carries 543 3456

/-
info: 2
-/
-- #guard_msgs in
-- #eval number_of_carries 1927 6426

/-
info: 4
-/
-- #guard_msgs in
-- #eval number_of_carries 9999 1

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible