import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polyfromroots",
  "category": "Standard polynomials",
  "description": "Generate a monic polynomial with given roots.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polyfromroots.html",
  "doc": "Generate a monic polynomial with given roots.\n\n    Return the coefficients of the polynomial\n\n    .. math:: p(x) = (x - r_0) * (x - r_1) * ... * (x - r_n),\n\n    where the :math:`r_n` are the roots specified in `roots`.  If a zero has\n    multiplicity n, then it must appear in `roots` n times. For instance,\n    if 2 is a root of multiplicity three and 3 is a root of multiplicity 2,\n    then `roots` looks something like [2, 2, 2, 3, 3]. The roots can appear\n    in any order.\n\n    If the returned coefficients are `c`, then\n\n    .. math:: p(x) = c_0 + c_1 * x + ... +  x^n\n\n    The coefficient of the last term is 1 for monic polynomials in this\n    form.\n\n    Parameters\n    ----------\n    roots : array_like\n        Sequence containing the roots.\n\n    Returns\n    -------\n    out : ndarray\n        1-D array of the polynomial's coefficients If all the roots are\n        real, then `out` is also real, otherwise it is complex.  (see\n        Examples below).\n\n    See Also\n    --------\n    numpy.polynomial.chebyshev.chebfromroots\n    numpy.polynomial.legendre.legfromroots\n    numpy.polynomial.laguerre.lagfromroots\n    numpy.polynomial.hermite.hermfromroots\n    numpy.polynomial.hermite_e.hermefromroots\n\n    Notes\n    -----\n    The coefficients are determined by multiplying together linear factors\n    of the form ``(x - r_i)``, i.e.\n\n    .. math:: p(x) = (x - r_0) (x - r_1) ... (x - r_n)\n\n    where ``n == len(roots) - 1``; note that this implies that ``1`` is always\n    returned for :math:`a_n`.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> P.polyfromroots((-1,0,1))  # x(x - 1)(x + 1) = x^3 - x\n    array([ 0., -1.,  0.,  1.])\n    >>> j = complex(0,1)\n    >>> P.polyfromroots((-j,j))  # complex returned, though values are real\n    array([1.+0.j,  0.+0.j,  1.+0.j])",
  "code": "def polyfromroots(roots):\n    \"\"\"\n    Generate a monic polynomial with given roots.\n\n    Return the coefficients of the polynomial\n\n    .. math:: p(x) = (x - r_0) * (x - r_1) * ... * (x - r_n),\n\n    where the :math:`r_n` are the roots specified in `roots`.  If a zero has\n    multiplicity n, then it must appear in `roots` n times. For instance,\n    if 2 is a root of multiplicity three and 3 is a root of multiplicity 2,\n    then `roots` looks something like [2, 2, 2, 3, 3]. The roots can appear\n    in any order.\n\n    If the returned coefficients are `c`, then\n\n    .. math:: p(x) = c_0 + c_1 * x + ... +  x^n\n\n    The coefficient of the last term is 1 for monic polynomials in this\n    form.\n\n    Parameters\n    ----------\n    roots : array_like\n        Sequence containing the roots.\n\n    Returns\n    -------\n    out : ndarray\n        1-D array of the polynomial's coefficients If all the roots are\n        real, then `out` is also real, otherwise it is complex.  (see\n        Examples below).\n\n    See Also\n    --------\n    numpy.polynomial.chebyshev.chebfromroots\n    numpy.polynomial.legendre.legfromroots\n    numpy.polynomial.laguerre.lagfromroots\n    numpy.polynomial.hermite.hermfromroots\n    numpy.polynomial.hermite_e.hermefromroots\n\n    Notes\n    -----\n    The coefficients are determined by multiplying together linear factors\n    of the form ``(x - r_i)``, i.e.\n\n    .. math:: p(x) = (x - r_0) (x - r_1) ... (x - r_n)\n\n    where ``n == len(roots) - 1``; note that this implies that ``1`` is always\n    returned for :math:`a_n`.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> P.polyfromroots((-1,0,1))  # x(x - 1)(x + 1) = x^3 - x\n    array([ 0., -1.,  0.,  1.])\n    >>> j = complex(0,1)\n    >>> P.polyfromroots((-j,j))  # complex returned, though values are real\n    array([1.+0.j,  0.+0.j,  1.+0.j])\n\n    \"\"\"\n    return pu._fromroots(polyline, polymul, roots)"
}
-/

/-- Generate a monic polynomial with given roots -/
def polyfromroots {n : Nat} (roots : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

/-- Specification: polyfromroots generates a monic polynomial with given roots.
    The resulting polynomial has the form p(x) = (x - r_0)(x - r_1)...(x - r_n),
    where the coefficients are returned in ascending order of powers. -/
theorem polyfromroots_spec {n : Nat} (roots : Vector Float n) :
    ⦃⌜True⌝⦄
    polyfromroots roots
    ⦃⇓coeffs => ⌜coeffs.get ⟨n, Nat.lt_succ_self n⟩ = 1 ∧
                 ∀ i : Fin n, ∃ (eval_poly : Float → Float), 
                   (∀ x : Float, eval_poly x = 0 ↔ x = roots.get i) ∧
                   eval_poly (roots.get i) = 0⌝⦄ := by
  sorry