import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagmulx",
  "category": "Laguerre polynomials",
  "description": "Multiply a Laguerre series by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagmulx.html",
  "doc": "Multiply a Laguerre series by x.\n\n    Multiply the Laguerre series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    lagadd, lagsub, lagmul, lagdiv, lagpow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Laguerre\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (-(i + 1)*P_{i + 1}(x) + (2i + 1)P_{i}(x) - iP_{i - 1}(x))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagmulx\n    >>> lagmulx([1, 2, 3])\n    array([-1.,  -1.,  11.,  -9.])",
  "code": "def lagmulx(c):\n    \"\"\"Multiply a Laguerre series by x.\n\n    Multiply the Laguerre series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    lagadd, lagsub, lagmul, lagdiv, lagpow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Laguerre\n    polynomials in the form\n\n    .. math::\n\n        xP_i(x) = (-(i + 1)*P_{i + 1}(x) + (2i + 1)P_{i}(x) - iP_{i - 1}(x))\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagmulx\n    >>> lagmulx([1, 2, 3])\n    array([-1.,  -1.,  11.,  -9.])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    # The zero series needs special treatment\n    if len(c) == 1 and c[0] == 0:\n        return c\n\n    prd = np.empty(len(c) + 1, dtype=c.dtype)\n    prd[0] = c[0]\n    prd[1] = -c[0]\n    for i in range(1, len(c)):\n        prd[i + 1] = -c[i] * (i + 1)\n        prd[i] += c[i] * (2 * i + 1)\n        prd[i - 1] -= c[i] * i\n    return prd"
}
-/

/-- Multiply a Laguerre series by x -/
def lagmulx {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float (n + 2)) :=
  sorry

/-- Specification: lagmulx multiplies a Laguerre series by x using the recursion relationship -/
theorem lagmulx_spec {n : Nat} (c : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    lagmulx c
    ⦃⇓result => ⌜result.size = n + 2 ∧ 
                 result.get 0 = c.get 0 ∧
                 result.get 1 = -c.get 0⌝⦄ := by
  sorry