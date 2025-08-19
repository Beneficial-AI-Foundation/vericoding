"""
NumPy Constants Module

This module consolidates all NumPy mathematical constants.
Each section contains both the implementation and documentation
for a specific constant.
"""

# =============================================================================
# Euler's constant (e)
# =============================================================================
"""Euler's constant, base of natural logarithms, Napier's constant.

e = 2.71828182845904523536028747135266249775724709369995...

See Also
--------
exp : Exponential function
log : Natural logarithm

References
----------
https://en.wikipedia.org/wiki/E_%28mathematical_constant%29
"""

def numpy_e() -> float:
    return 2.71828182845904523536028747135266249775724709369995 


# =============================================================================
# Euler-Mascheroni constant (gamma)
# =============================================================================
"""γ = 0.5772156649015328606065120900824024310421...

References
----------
https://en.wikipedia.org/wiki/Euler%27s_constant
"""

def numpy_euler_gamma() -> float:
    return 0.5772156649015328606065120900824024310421 


# =============================================================================
# Infinity
# =============================================================================
"""IEEE 754 floating point representation of (positive) infinity.

Returns
-------
y : float
    A floating point representation of positive infinity.

See Also
--------
isinf : Shows which elements are positive or negative infinity
isposinf : Shows which elements are positive infinity
isneginf : Shows which elements are negative infinity
isnan : Shows which elements are Not a Number
isfinite : Shows which elements are finite (not one of Not a Number, positive infinity and negative infinity)

Notes
-----
NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic (IEEE 754). This means that Not a Number is not equivalent to infinity. Also that positive infinity is not equivalent to negative infinity. But infinity is equivalent to positive infinity.
"""

def numpy_inf() -> float:
    return float("inf") 


# =============================================================================
# Not a Number (NaN)
# =============================================================================
"""IEEE 754 floating point representation of Not a Number (NaN).

Returns
-------
y : float
    A floating point representation of Not a Number.

See Also
--------
isnan : Shows which elements are Not a Number.

isfinite : Shows which elements are finite (not one of Not a Number, positive infinity and negative infinity)

Notes
-----
NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic (IEEE 754). This means that Not a Number is not equivalent to infinity.
"""

def numpy_nan() -> float:
    return float("nan") 