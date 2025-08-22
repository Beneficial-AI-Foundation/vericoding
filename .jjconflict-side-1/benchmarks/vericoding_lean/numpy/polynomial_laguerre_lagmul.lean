import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagmul",
  "category": "Laguerre polynomials",
  "description": "Multiply one Laguerre series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagmul.html",
  "doc": "Multiply one Laguerre series by another.\n\n    Returns the product of two Laguerre series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Laguerre series coefficients representing their product.\n\n    See Also\n    --------\n    lagadd, lagsub, lagmulx, lagdiv, lagpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Laguerre polynomial basis set.  Thus, to express\n    the product as a Laguerre series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagmul\n    >>> lagmul([1, 2, 3], [0, 1, 2])\n    array([  8., -13.,  38., -51.,  36.])",
  "code": "def lagmul(c1, c2):\n    \"\"\"\n    Multiply one Laguerre series by another.\n\n    Returns the product of two Laguerre series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Laguerre series coefficients representing their product.\n\n    See Also\n    --------\n    lagadd, lagsub, lagmulx, lagdiv, lagpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Laguerre polynomial basis set.  Thus, to express\n    the product as a Laguerre series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagmul\n    >>> lagmul([1, 2, 3], [0, 1, 2])\n    array([  8., -13.,  38., -51.,  36.])\n\n    \"\"\"\n    # s1, s2 are trimmed copies\n    [c1, c2] = pu.as_series([c1, c2])\n\n    if len(c1) > len(c2):\n        c = c2\n        xs = c1\n    else:\n        c = c1\n        xs = c2\n\n    if len(c) == 1:\n        c0 = c[0] * xs\n        c1 = 0\n    elif len(c) == 2:\n        c0 = c[0] * xs\n        c1 = c[1] * xs\n    else:\n        nd = len(c)\n        c0 = c[-2] * xs\n        c1 = c[-1] * xs\n        for i in range(3, len(c) + 1):\n            tmp = c0\n            nd = nd - 1\n            c0 = lagsub(c[-i] * xs, (c1 * (nd - 1)) / nd)\n            c1 = lagadd(tmp, lagsub((2 * nd - 1) * c1, lagmulx(c1)) / nd)\n    return lagadd(c0, lagsub(c1, lagmulx(c1)))"
}
-/

/-- Multiply one Laguerre series by another -/
def lagmul {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) : Id (Vector Float (n + m + 1)) :=
  sorry

/-- Specification: lagmul returns the product of two Laguerre series in coefficient form -/
theorem lagmul_spec {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) :
    ⦃⌜True⌝⦄
    lagmul c1 c2
    ⦃⇓result => ⌜result.size = n + m + 1 ∧ 
                 ∀ i : Fin (n + m + 1), result.get i ≠ 0 → 
                   ∃ (j : Fin (n + 1)) (k : Fin (m + 1)), 
                     j.val + k.val = i.val ∧ c1.get j ≠ 0 ∧ c2.get k ≠ 0⌝⦄ := by
  sorry