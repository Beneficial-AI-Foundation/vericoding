/* {
  "name": "numpy.polynomial.polynomial.polypow",
  "category": "Standard polynomials",
  "description": "Raise a polynomial to a power.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polypow.html",
  "doc": "Raise a polynomial to a power.\n\n    Returns the polynomial \`c\` raised to the power \`pow\`. The argument\n    \`c\` is a sequence of coefficients ordered from low to high. i.e.,\n    [1,2,3] is the series  \`\`1 + 2*x + 3*x**2.\`\`\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of array of series coefficients ordered from low to\n        high degree.\n    pow : integer\n        Power to which the series will be raised\n    maxpower : integer, optional\n        Maximum power allowed. This is mainly to limit growth of the series\n        to unmanageable size. Default is 16\n\n    Returns\n    -------\n    coef : ndarray\n        Power series of power.\n\n    See Also\n    --------\n    polyadd, polysub, polymulx, polymul, polydiv\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> P.polypow([1, 2, 3], 2)\n    array([ 1., 4., 10., 12., 9.])"
}

Raise a polynomial to a power.
Returns the polynomial c raised to the power pow.
For polynomial p(x) = c[0] + c[1]*x + ... + c[n-1]*x^(n-1),
returns p(x)^pow with appropriate coefficient expansion.

Specification: polypow raises a polynomial to a non-negative integer power.
The result represents the polynomial p(x)^pow where p(x) is defined by coefficients c.
For power 0, returns [1] (the constant polynomial 1).
For power 1, returns the original polynomial.
The degree grows as expected for polynomial multiplication. */

use vstd::prelude::*;

verus! {
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> result.len() == 1 && result[0] == 1.0f32,
        pow == 1 ==> result.len() == c.len() && forall|i: int| 0 <= i < c.len() ==> result[i] == c[i],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}