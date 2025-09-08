/-
Complete the function that calculates the derivative of a polynomial. A polynomial is an expression like: 3x^(4) - 2x^(2) + x - 10

### How to calculate the derivative:

* Take the exponent and multiply it with the coefficient
* Reduce the exponent by 1

For example: 3x^(4) --> (4*3)x^((4-1)) = 12x^(3)

### Good to know:

* The derivative of a constant is 0 (e.g. 100 --> 0)
* Anything to the 0th exponent equals 1 (e.g. x^(0) = 1)
* The derivative of the sum of two function is the sum of the derivatives

Notes:
* The exponentiation is marked with "^"
* Exponents are always integers and >= 0
* Exponents are written only if > 1
* There are no spaces around the operators
* Leading "+" signs are omitted

See the examples below.

## Examples
```python
derivative("-100")      = "0"
derivative("4x+1")      = "4"      # = 4x^0 + 0
derivative("-x^2+3x+4") = "-2x+3"  # = -2x^1 + 3x^0 + 0
```
-/

-- <vc-helpers>
-- </vc-helpers>

def derivative (s : String) : String := sorry

theorem derivative_constant (n : Nat) (h : n > 0 ∧ n ≤ 100) : 
  derivative s!"${n}x" = s!"${n}" := sorry

theorem derivative_power_rule (n : Nat) (h : n > 0 ∧ n ≤ 10) :
  derivative s!"x^${n}" = 
    if n > 2 then s!"${n}x^${n-1}"
    else if n = 2 then s!"${n}x"
    else "1" := sorry

theorem derivative_linearity (s : String) :
  ∃ result : String, derivative s = result ∧ result.length > 0 := sorry

/-
info: '4'
-/
-- #guard_msgs in
-- #eval derivative "4x+1"

/-
info: '-2x+3'
-/
-- #guard_msgs in
-- #eval derivative "-x^2+3x+4"

/-
info: '2x+2'
-/
-- #guard_msgs in
-- #eval derivative "x^2+2x+1"

-- Apps difficulty: introductory
-- Assurance level: unguarded