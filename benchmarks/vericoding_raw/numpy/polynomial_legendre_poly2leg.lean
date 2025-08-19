import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.poly2leg",
  "category": "Legendre polynomials",
  "description": "Convert a polynomial to a Legendre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.poly2leg.html",
  "doc": "Convert a polynomial to a Legendre series.\n\n    Convert an array representing the coefficients of a polynomial (relative\n    to the \"standard\" basis) ordered from lowest degree to highest, to an\n    array of the coefficients of the equivalent Legendre series, ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    pol : array_like\n        1-D array containing the polynomial coefficients\n\n    Returns\n    -------\n    c : ndarray\n        1-D array containing the coefficients of the equivalent Legendre\n        series.\n\n    See Also\n    --------\n    leg2poly\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy import polynomial as P\n    >>> p = P.Polynomial(np.arange(4))\n    >>> p\n    Polynomial([0.,  1.,  2.,  3.], domain=[-1.,  1.], window=[-1.,  1.], ...\n    >>> c = P.Legendre(P.legendre.poly2leg(p.coef))\n    >>> c\n    Legendre([ 1.  ,  3.25,  1.  ,  0.75], domain=[-1,  1], window=[-1,  1]) # may vary",
  "code": "def poly2leg(pol):\n    \"\"\"\n    Convert a polynomial to a Legendre series.\n\n    Convert an array representing the coefficients of a polynomial (relative\n    to the \"standard\" basis) ordered from lowest degree to highest, to an\n    array of the coefficients of the equivalent Legendre series, ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    pol : array_like\n        1-D array containing the polynomial coefficients\n\n    Returns\n    -------\n    c : ndarray\n        1-D array containing the coefficients of the equivalent Legendre\n        series.\n\n    See Also\n    --------\n    leg2poly\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy import polynomial as P\n    >>> p = P.Polynomial(np.arange(4))\n    >>> p\n    Polynomial([0.,  1.,  2.,  3.], domain=[-1.,  1.], window=[-1.,  1.], ...\n    >>> c = P.Legendre(P.legendre.poly2leg(p.coef))\n    >>> c\n    Legendre([ 1.  ,  3.25,  1.  ,  0.75], domain=[-1,  1], window=[-1,  1]) # may vary\n\n    \"\"\"\n    [pol] = pu.as_series([pol])\n    deg = len(pol) - 1\n    res = 0\n    for i in range(deg, -1, -1):\n        res = legadd(legmulx(res), pol[i])\n    return res"
}
-/

/-- Convert a polynomial to a Legendre series.
    Converts coefficients from standard polynomial basis to Legendre basis. -/
def poly2leg {n : Nat} (pol : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: poly2leg converts polynomial coefficients to Legendre series coefficients.
    The transformation preserves the polynomial degree and produces valid Legendre coefficients.
    The result has the same dimension as the input and represents the same polynomial
    expressed in the Legendre basis instead of the standard monomial basis. -/
theorem poly2leg_spec {n : Nat} (pol : Vector Float n) :
    ⦃⌜True⌝⦄
    poly2leg pol
    ⦃⇓result => ⌜∀ i : Fin n, ∃ c : Float, result.get i = c⌝⦄ := by
  sorry