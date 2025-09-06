/- 
{
  "name": "numpy.polynomial.polynomial.polyroots",
  "category": "Standard polynomials",
  "description": "Compute the roots of a polynomial.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polyroots.html",
  "doc": "Compute the roots of a polynomial.\n\n    Return the roots (a.k.a. \"zeros\") of the polynomial\n\n    .. math:: p(x) = \\sum_i c[i] * x^i.\n\n    Parameters\n    ----------\n    c : 1-D array_like\n        1-D array of polynomial coefficients.\n\n    Returns\n    -------\n    out : ndarray\n        Array of the roots of the polynomial. If all the roots are real,\n        then `out` is also real, otherwise it is complex.\n\n    See Also\n    --------\n    numpy.polynomial.chebyshev.chebroots\n    numpy.polynomial.legendre.legroots\n    numpy.polynomial.laguerre.lagroots\n    numpy.polynomial.hermite.hermroots\n    numpy.polynomial.hermite_e.hermeroots\n\n    Notes\n    -----\n    The root estimates are obtained as the eigenvalues of the companion\n    matrix, Roots far from the origin of the complex plane may have large\n    errors due to the numerical instability of the power series for such\n    values. Roots with multiplicity greater than 1 will also show larger\n    errors as the value of the series near such points is relatively\n    insensitive to errors in the roots. Isolated roots near the origin can\n    be improved by a few iterations of Newton's method.\n\n    Examples\n    --------\n    >>> import numpy.polynomial.polynomial as poly\n    >>> poly.polyroots(poly.polyfromroots((-1,0,1)))\n    array([-1.,  0.,  1.])\n    >>> poly.polyroots(poly.polyfromroots((-1,0,1))).dtype\n    dtype('float64')\n    >>> j = complex(0,1)\n    >>> poly.polyroots(poly.polyfromroots((-j,0,j)))\n    array([  0.00000000e+00+0.j,   0.00000000e+00+1.j,   2.77555756e-17-1.j])  # may vary",
}
-/

/-  Compute the roots of a polynomial.
    Given polynomial coefficients c[0], c[1], ..., c[n-1], returns the roots of
    p(x) = c[0] + c[1]*x + c[2]*x^2 + ... + c[n-1]*x^(n-1).
    For a polynomial of degree n, there are exactly n roots (counting multiplicity). -/

/-  Specification: polyroots returns the roots of the polynomial defined by coefficients.
    For a polynomial p(x) = Σ c[i] * x^i with degree n (where c[n] ≠ 0), 
    there are exactly n roots (counting multiplicity).
    The polynomial must be non-constant (degree ≥ 1). -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyroots {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float n) :=
  sorry

theorem polyroots_spec {n : Nat} (c : Vector Float (n + 1)) 
    (h_nonzero : c.get ⟨n, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n, by omega⟩ ≠ 0⌝⦄
    polyroots c
    ⦃⇓roots => ⌜∀ i : Fin n, ∃ j : Fin (n + 1), c.get j ≠ 0⌝⦄ := by
  sorry
