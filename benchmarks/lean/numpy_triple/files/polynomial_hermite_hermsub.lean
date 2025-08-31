/- 
{
  "name": "numpy.polynomial.hermite.hermsub",
  "category": "Hermite polynomials",
  "description": "Subtract one Hermite series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermsub.html",
  "doc": "Subtract one Hermite series from another.\n\n    Returns the difference of two Hermite series `c1` - `c2`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series ``P_0 + 2*P_1 + 3*P_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Hermite series coefficients representing their difference.\n\n    See Also\n    --------\n    hermadd, hermmulx, hermmul, hermdiv, hermpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Hermite\n    series is a Hermite series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermsub\n    >>> hermsub([1, 2, 3, 4], [1, 2, 3])\n    array([0.,  0.,  0.,  4.])",
}
-/

/-  Subtract one Hermite series from another.
    
    Returns the difference of two Hermite series c1 - c2. The sequences of coefficients 
    are from lowest order term to highest. The subtraction is component-wise, with 
    missing coefficients treated as zero. -/

/-  Specification: hermsub performs component-wise subtraction of Hermite series coefficients,
    treating missing coefficients as zero. The result has the length of the longer input. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermsub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : 
    Id (Vector Float (max n m)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem hermsub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermsub c1 c2
    ⦃⇓result => ⌜
      -- For indices within both arrays, result is the difference
      (∀ i : Nat, i < min n m → 
        result.get ⟨i, sorry⟩ = c1.get ⟨i, sorry⟩ - c2.get ⟨i, sorry⟩) ∧
      -- For indices beyond c2's length (when n > m), result equals c1
      (n > m → ∀ i : Nat, m ≤ i ∧ i < n → 
        result.get ⟨i, sorry⟩ = c1.get ⟨i, sorry⟩) ∧
      -- For indices beyond c1's length (when m > n), result equals negation of c2
      (m > n → ∀ i : Nat, n ≤ i ∧ i < m → 
        result.get ⟨i, sorry⟩ = -c2.get ⟨i, sorry⟩)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
