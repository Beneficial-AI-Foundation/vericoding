/-
Write a function named sumDigits which takes a number as input and returns the sum of the absolute value of each of the number's decimal digits.  For example:

```python
  sum_digits(10)  # Returns 1
  sum_digits(99)  # Returns 18
  sum_digits(-32) # Returns 5
```

Let's assume that all numbers in the input will be integer values.
-/

def sum_digits (n : Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_of_digits_string (n : Int) : Int :=
  sorry

theorem sum_digits_nonnegative (x : Int) :
  sum_digits x ≥ 0 :=
  sorry

theorem sum_digits_symmetric (x : Int) :
  sum_digits x = sum_digits (-x) :=
  sorry

theorem sum_digits_less_than_input (x : Int) (h : x.natAbs > 9) :
  sum_digits x < x.natAbs :=
  sorry

theorem sum_digits_single_digit (x : Int) 
  (h : 0 ≤ x.natAbs ∧ x.natAbs ≤ 9) :
  sum_digits x = x.natAbs :=
  sorry

theorem sum_digits_matches_string_sum (x : Int) :
  x ≥ 0 → sum_digits x = sum_of_digits_string x :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_digits 10

/-
info: 18
-/
-- #guard_msgs in
-- #eval sum_digits 99

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_digits -32

-- Apps difficulty: introductory
-- Assurance level: unguarded