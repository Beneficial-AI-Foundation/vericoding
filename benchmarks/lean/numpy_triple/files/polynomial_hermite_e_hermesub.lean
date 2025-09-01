/- 
{
  "name": "numpy.polynomial.hermite_e.hermesub",
  "category": "HermiteE polynomials",
  "description": "Subtract one Hermite series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermesub.html",
  "doc": "Subtract one Hermite series from another.\n\n    Returns the difference of two Hermite series \`c1\` - \`c2\`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Hermite series coefficients representing their difference.\n\n    See Also\n    --------\n    hermeadd, hermemulx, hermemul, hermediv, hermepow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Hermite\n    series is a Hermite series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermesub\n    >>> hermesub([1, 2, 3, 4], [1, 2, 3])\n    array([0., 0., 0., 4.])",
}
-/

/-  Subtract one Hermite series from another.
    Returns the difference of two Hermite series c1 - c2.
    The sequences of coefficients are from lowest order term to highest. -/

/-  Specification: hermesub performs component-wise subtraction of Hermite series coefficients.
    The result has length equal to the maximum of the input lengths, with shorter arrays
    implicitly padded with zeros. This captures the mathematical property that polynomial 
    subtraction is component-wise and preserves the polynomial structure. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermesub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem hermesub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermesub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
      result.get i = (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else 0) - 
                     (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
