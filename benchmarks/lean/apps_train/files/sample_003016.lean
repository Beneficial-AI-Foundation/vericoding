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

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
