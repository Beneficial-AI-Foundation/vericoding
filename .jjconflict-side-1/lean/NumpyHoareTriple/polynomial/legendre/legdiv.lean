import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legdiv",
  "category": "Legendre polynomials",
  "description": "Divide one Legendre series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legdiv.html",
  "doc": "Divide one Legendre series by another.\n\n    Returns the quotient-with-remainder of two Legendre series\n    \`c1\` / \`c2\`.  The arguments are sequences of coefficients from lowest\n    order \"term\" to highest, e.g., [1,2,3] represents the series\n    \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    quo, rem : ndarrays\n        Of Legendre series coefficients representing the quotient and\n        remainder.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legmul, legpow\n\n    Notes\n    -----\n    In general, the (polynomial) division of one Legendre series by another\n    results in quotient and remainder terms that are not in the Legendre\n    polynomial basis set.  Thus, to express these results as a Legendre\n    series, it is necessary to \"reproject\" the results onto the Legendre\n    basis set, which may produce \"unintuitive\" (but correct) results; see\n    Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legdiv(c1,c2) # quotient \"intuitive,\" remainder not\n    (array([3.]), array([-8., -4.]))\n    >>> c2 = (0,1,2,3)\n    >>> L.legdiv(c2,c1) # neither \"intuitive\"\n    (array([-0.07407407,  1.66666667]), array([-1.03703704, -2.51851852])) # may vary",
  "code": "def legdiv(c1, c2):\n    \"\"\"\n    Divide one Legendre series by another.\n\n    Returns the quotient-with-remainder of two Legendre series\n    \`c1\` / \`c2\`.  The arguments are sequences of coefficients from lowest\n    order \"term\" to highest, e.g., [1,2,3] represents the series\n    \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    quo, rem : ndarrays\n        Of Legendre series coefficients representing the quotient and\n        remainder.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legmul, legpow\n\n    Notes\n    -----\n    In general, the (polynomial) division of one Legendre series by another\n    results in quotient and remainder terms that are not in the Legendre\n    polynomial basis set.  Thus, to express these results as a Legendre\n    series, it is necessary to \"reproject\" the results onto the Legendre\n    basis set, which may produce \"unintuitive\" (but correct) results; see\n    Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legdiv(c1,c2) # quotient \"intuitive,\" remainder not\n    (array([3.]), array([-8., -4.]))\n    >>> c2 = (0,1,2,3)\n    >>> L.legdiv(c2,c1) # neither \"intuitive\"\n    (array([-0.07407407,  1.66666667]), array([-1.03703704, -2.51851852])) # may vary\n\n    \"\"\"\n    return pu._div(legmul, c1, c2)"
}
-/

/-- Divide one Legendre series by another.
    Returns the quotient and remainder of two Legendre series c1 / c2.
    The arguments are sequences of coefficients from lowest order to highest. -/
def legdiv {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m)
    : Id (Vector Float (max 1 (n - m + 1)) × Vector Float (max 1 (m - 1))) :=
  sorry

/-- Specification: legdiv computes polynomial division in Legendre basis -/
theorem legdiv_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m)
    (h_n : n ≥ 1) (h_m : m ≥ 1) (h_nonzero : ∃ i : Fin m, c2.get i ≠ 0) :
    ⦃⌜n ≥ 1 ∧ m ≥ 1 ∧ ∃ i : Fin m, c2.get i ≠ 0⌝⦄
    legdiv c1 c2
    ⦃⇓result => ⌜
      let quo := result.1
      let rem := result.2
      -- Quotient has correct size
      (quo.size = max 1 (n - m + 1)) ∧
      -- Remainder has correct size
      (rem.size = max 1 (m - 1)) ∧
      -- Division property: when dividend degree < divisor degree, quotient is zero
      (n < m → quo.size = 1 ∧ ∃ h : 0 < quo.size, quo.get ⟨0, h⟩ = 0) ∧
      -- Remainder size constraint
      (rem.size ≤ m)
    ⌝⦄ := by
  sorry
