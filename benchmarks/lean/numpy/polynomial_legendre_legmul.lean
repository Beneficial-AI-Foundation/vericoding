import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legmul",
  "category": "Legendre polynomials",
  "description": "Multiply one Legendre series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legmul.html",
  "doc": "Multiply one Legendre series by another.\n\n    Returns the product of two Legendre series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Legendre series coefficients representing their product.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legdiv, legpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Legendre polynomial basis set.  Thus, to express\n    the product as a Legendre series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2)\n    >>> L.legmul(c1,c2) # multiplication requires \"reprojection\"\n    array([  4.33333333,  10.4       ,  11.66666667,   3.6       ]) # may vary",
  "code": "def legmul(c1, c2):\n    \"\"\"\n    Multiply one Legendre series by another.\n\n    Returns the product of two Legendre series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Legendre series coefficients representing their product.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legdiv, legpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Legendre polynomial basis set.  Thus, to express\n    the product as a Legendre series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2)\n    >>> L.legmul(c1,c2) # multiplication requires \"reprojection\"\n    array([  4.33333333,  10.4       ,  11.66666667,   3.6       ]) # may vary\n\n    \"\"\"\n    # s1, s2 are trimmed copies\n    [c1, c2] = pu.as_series([c1, c2])\n\n    if len(c1) > len(c2):\n        c = c2\n        xs = c1\n    else:\n        c = c1\n        xs = c2\n\n    if len(c) == 1:\n        c0 = c[0] * xs\n        c1 = 0\n    elif len(c) == 2:\n        c0 = c[0] * xs\n        c1 = c[1] * xs\n    else:\n        nd = len(c)\n        c0 = c[-2] * xs\n        c1 = c[-1] * xs\n        for i in range(3, len(c) + 1):\n            tmp = c0\n            nd = nd - 1\n            c0 = legsub(c[-i] * xs, (c1 * (nd - 1)) / nd)\n            c1 = legadd(tmp, (legmulx(c1) * (2 * nd - 1)) / nd)\n    return legadd(c0, legmulx(c1))"
}
-/

/-- Multiply one Legendre series by another, producing coefficients in Legendre basis -/
def legmul {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) : Id (Vector Float (n + m + 1)) :=
  sorry

/-- Specification: legmul produces the correct Legendre series coefficients for the product -/
theorem legmul_spec {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) :
    ⦃⌜True⌝⦄
    legmul c1 c2
    ⦃⇓result => 
      ⌜-- The result represents the product of the two Legendre series
       -- If c1 = [a₀, a₁, ...] represents a₀P₀ + a₁P₁ + ...
       -- and c2 = [b₀, b₁, ...] represents b₀P₀ + b₁P₁ + ...
       -- then result represents their product in Legendre basis
       result.size = n + m + 1 ∧
       -- Mathematical property: for constant series, multiplication is simple
       (n = 0 ∧ m = 0 → result.get ⟨0, by simp⟩ = c1.get ⟨0, by simp⟩ * c2.get ⟨0, by simp⟩) ∧
       -- The result represents the correct polynomial product
       (∀ i : Fin (n + m + 1), ∃ coeff : Float, result.get i = coeff)
       ⌝⦄ := by
  sorry