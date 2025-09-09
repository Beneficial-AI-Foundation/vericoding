/-
*Debug*   function `getSumOfDigits` that takes positive integer to calculate sum of it's digits. Assume that argument is an integer.

### Example
```
123  => 6
223  => 7
1337 => 15
```
-/

-- <vc-helpers>
-- </vc-helpers>

def getSumOfDigits (n : Nat) : Nat :=
  sorry

theorem sum_digits_basic_property (n : Nat) :
  getSumOfDigits n ≤ n :=
  sorry

theorem sum_digits_upper_bound (n : Nat) :
  getSumOfDigits n ≤ 9 * (toString n).length :=
  sorry

theorem sum_digits_non_negative (n : Nat) :
  getSumOfDigits n ≥ 0 :=
  sorry

theorem single_digit_identity (n : Nat) :
  n < 10 → getSumOfDigits n = n :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded