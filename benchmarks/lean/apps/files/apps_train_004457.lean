/-
Write a program that will calculate the number of trailing zeros in a factorial of a given number.

`N! = 1 * 2 * 3 *  ... * N`

Be careful `1000!` has 2568 digits...

For more info, see: http://mathworld.wolfram.com/Factorial.html 

## Examples

```python
zeros(6) = 1
# 6! = 1 * 2 * 3 * 4 * 5 * 6 = 720 --> 1 trailing zero

zeros(12) = 2
# 12! = 479001600 --> 2 trailing zeros
```

*Hint: You're not meant to calculate the factorial. Find another way to find the number of zeros.*
-/

-- <vc-helpers>
-- </vc-helpers>

def zeros (n : Nat) : Nat := sorry

theorem zeros_non_negative (n : Nat) :
  zeros n ≥ 0 := sorry

theorem zeros_monotonic (n : Nat) :
  n > 0 → zeros n ≥ zeros (n-1) := sorry

theorem zeros_less_than_input (n : Nat) :
  n > 0 → zeros n < n := sorry

theorem zeros_small_inputs :
  zeros 0 = 0 ∧ zeros 1 = 0 ∧ zeros 4 = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval zeros 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval zeros 6

/-
info: 7
-/
-- #guard_msgs in
-- #eval zeros 30

-- Apps difficulty: introductory
-- Assurance level: unguarded