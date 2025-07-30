import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.legendre.legadd",
  "category": "Legendre polynomials",
  "description": "Add one Legendre series to another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legadd.html",
  "doc": "Add one Legendre series to another.\n\n    Returns the sum of two Legendre series `c1` + `c2`.  The arguments\n    are sequences of coefficients ordered from lowest order term to\n    highest, i.e., [1,2,3] represents the series ``P_0 + 2*P_1 + 3*P_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the Legendre series of their sum.\n\n    See Also\n    --------\n    legsub, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the sum of two Legendre series\n    is a Legendre series (without having to \"reproject\" the result onto\n    the basis set) so addition, just like that of \"standard\" polynomials,\n    is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legadd(c1,c2)\n    array([4.,  4.,  4.])",
  "code": "def legadd(c1, c2):\n    \"\"\"\n    Add one Legendre series to another.\n\n    Returns the sum of two Legendre series `c1` + `c2`.  The arguments\n    are sequences of coefficients ordered from lowest order term to\n    highest, i.e., [1,2,3] represents the series ``P_0 + 2*P_1 + 3*P_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the Legendre series of their sum.\n\n    See Also\n    --------\n    legsub, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the sum of two Legendre series\n    is a Legendre series (without having to \"reproject\" the result onto\n    the basis set) so addition, just like that of \"standard\" polynomials,\n    is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legadd(c1,c2)\n    array([4.,  4.,  4.])\n\n    \"\"\"\n    return pu._add(c1, c2)"
}
-/

open Std.Do

/-- Add one Legendre series to another by component-wise addition of coefficients -/
def legadd {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  sorry

/-- Specification: legadd performs component-wise addition of two Legendre series coefficients -/
theorem legadd_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    legadd c1 c2
    ⦃⇓result => ⌜
      -- Each coefficient is the sum of corresponding coefficients
      ∀ i : Fin (max n m), 
        result.get i = 
          (if h1 : i.val < n then c1.get ⟨i.val, h1⟩ else 0) +
          (if h2 : i.val < m then c2.get ⟨i.val, h2⟩ else 0)
    ⌝⦄ := by
  sorry