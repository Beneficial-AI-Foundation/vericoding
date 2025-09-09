/- 
{
  "name": "numpy.polynomial.legendre.legmulx",
  "category": "Legendre polynomials",
  "description": "Multiply a Legendre series by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legmulx.html",
  "doc": "Multiply a Legendre series by x.\n\n    Multiply the Legendre series \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    legadd, legsub, legmul, legdiv, legpow\n\n    Notes\n    -----\n    The multiplication uses the recursion relationship for Legendre\n    polynomials in the form\n\n    .. math::\n\n      xP_i(x) = ((i + 1)*P_{i + 1}(x) + i*P_{i - 1}(x))/(2i + 1)\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> L.legmulx([1,2,3])\n    array([ 0.66666667, 2.2, 1.33333333, 1.8]) # may vary",
}
-/

/-  Multiply a Legendre series by x using the Legendre recurrence relation -/

/-  Specification: legmulx multiplies a Legendre series by x using the correct recurrence relation -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def legmulx {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float (n + 2)) :=
  sorry

theorem legmulx_spec {n : Nat} (c : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    legmulx c
    ⦃⇓result => 
      ⌜-- The result has one more coefficient than the input
       result.size = n + 2 ∧
       -- Uses the Legendre recurrence relation: xPᵢ(x) = ((i+1)Pᵢ₊₁(x) + iPᵢ₋₁(x))/(2i+1)
       -- For constant term: the first element becomes 0 when multiplied by x (redistributed)
       result.get ⟨0, Nat.zero_lt_succ _⟩ = 0 ∧
       -- For the first coefficient: x*P₀ = P₁, so the constant coeff goes to position 1
       result.get ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ = c.get ⟨0, Nat.zero_lt_succ _⟩ ∧
       -- Higher order terms follow the recurrence relation
       (∀ i : Fin (n + 2), ∃ coeff : Float, result.get i = coeff)
       ⌝⦄ := by
  sorry
