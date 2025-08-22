import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polymulx",
  "category": "Standard polynomials",
  "description": "Multiply a polynomial by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polymulx.html",
  "doc": "Multiply a polynomial by x.\n\n    Multiply the polynomial \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of polynomial coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    polyadd, polysub, polymul, polydiv, polypow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = (1, 2, 3)\n    >>> P.polymulx(c)\n    array([0., 1., 2., 3.])",
  "code": "def polymulx(c):\n    \"\"\"Multiply a polynomial by x.\n\n    Multiply the polynomial \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of polynomial coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    polyadd, polysub, polymul, polydiv, polypow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = (1, 2, 3)\n    >>> P.polymulx(c)\n    array([0., 1., 2., 3.])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    # The zero series needs special treatment\n    if len(c) == 1 and c[0] == 0:\n        return c\n\n    prd = np.empty(len(c) + 1, dtype=c.dtype)\n    prd[0] = c[0] * 0\n    prd[1:] = c\n    return prd"
}
-/

open Std.Do

/-- Multiply a polynomial by x.
    Multiplies polynomial c by x, where x is the independent variable.
    For polynomial p(x) = c[0] + c[1]*x + ... + c[n-1]*x^(n-1),
    returns x*p(x) = 0 + c[0]*x + c[1]*x^2 + ... + c[n-1]*x^n -/
def polymulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

/-- Specification: polymulx multiplies a polynomial by x.
    The result has one more coefficient than the input.
    The first coefficient is always 0, and subsequent coefficients
    are the original coefficients shifted by one position.
    This represents multiplying p(x) by x to get x*p(x). -/
theorem polymulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    polymulx c
    ⦃⇓result => ⌜result.get ⟨0, by simp⟩ = 0 ∧ 
                 ∀ i : Fin n, result.get ⟨i.val + 1, by simp⟩ = c.get i⌝⦄ := by
  sorry