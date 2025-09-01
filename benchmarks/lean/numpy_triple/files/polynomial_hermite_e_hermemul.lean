/- 
{
  "name": "numpy.polynomial.hermite_e.hermemul",
  "category": "HermiteE polynomials",
  "description": "Multiply one Hermite series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermemul.html",
  "doc": "Multiply one Hermite series by another.\n\n    Returns the product of two Hermite series \`c1\` * \`c2\`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Hermite series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Hermite series coefficients representing their product.\n\n    See Also\n    --------\n    hermeadd, hermesub, hermemulx, hermediv, hermepow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Hermite polynomial basis set.  Thus, to express\n    the product as a Hermite series, it is necessary to \"reproject\" the\n    product onto said basis set, which may produce \"unintuitive\" (but\n    correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite_e import hermemul\n    >>> hermemul([1, 2, 3], [0, 1, 2])\n    array([14.,  15.,  28.,   7.,   6.])",
}
-/

/-  Multiply one Hermite series by another. Returns the product of two Hermite polynomials 
    represented as coefficient vectors. The multiplication involves reprojection onto 
    the Hermite polynomial basis set. -/

/-  Specification: hermemul computes the product of two Hermite series.
    
    Mathematical background: For Hermite polynomials, multiplication is not component-wise
    but requires reprojection onto the Hermite polynomial basis. Given two Hermite series:
    - P₁(x) = c1[0]H₀(x) + c1[1]H₁(x) + ... + c1[n-1]Hₙ₋₁(x)
    - P₂(x) = c2[0]H₀(x) + c2[1]H₁(x) + ... + c2[m-1]Hₘ₋₁(x)
    
    The product P₁(x) * P₂(x) must be expressed as a linear combination of Hermite polynomials.
    
    Properties verified:
    1. Commutativity: hermemul c1 c2 = hermemul c2 c1 (when extended to same size)
    2. Bilinearity: multiplication distributes over addition
    3. Zero preservation: if all coefficients of c1 or c2 are zero, then result is zero
    4. Degree bound: the result has at most n + m - 1 coefficients
    5. Non-degeneracy: non-zero inputs produce non-zero output
    -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermemul {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (n + m - 1)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem hermemul_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) 
    (h_n : n > 0) (h_m : m > 0) :
    ⦃⌜n > 0 ∧ m > 0⌝⦄
    hermemul c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, c1.get i = 0) ∨ (∀ j : Fin m, c2.get j = 0) → 
                   (∀ k : Fin (n + m - 1), result.get k = 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
