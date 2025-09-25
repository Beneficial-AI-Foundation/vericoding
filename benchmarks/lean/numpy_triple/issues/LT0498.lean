-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legpow",
  "category": "Legendre polynomials",
  "description": "Raise a Legendre series to a power.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legpow.html",
  "doc": "Raise a Legendre series to a power.\n\n    Returns the Legendre series \`c\` raised to the power \`pow\`. The\n    argument \`c\` is a sequence of coefficients ordered from low to high.\n    i.e., [1,2,3] is the series  \`\`P_0 + 2*P_1 + 3*P_2.\`\`\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Legendre series coefficients ordered from low to\n        high.\n    pow : integer\n        Power to which the series will be raised\n    maxpower : integer, optional\n        Maximum power allowed. This is mainly to limit growth of the series\n        to unmanageable size. Default is 16\n\n    Returns\n    -------\n    coef : ndarray\n        Legendre series of power.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legmul, legdiv",
  "code": "def legpow(c, pow, maxpower=16):\n    \"\"\"Raise a Legendre series to a power.\n\n    Returns the Legendre series \`c\` raised to the power \`pow\`. The\n    argument \`c\` is a sequence of coefficients ordered from low to high.\n    i.e., [1,2,3] is the series  \`\`P_0 + 2*P_1 + 3*P_2.\`\`\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Legendre series coefficients ordered from low to\n        high.\n    pow : integer\n        Power to which the series will be raised\n    maxpower : integer, optional\n        Maximum power allowed. This is mainly to limit growth of the series\n        to unmanageable size. Default is 16\n\n    Returns\n    -------\n    coef : ndarray\n        Legendre series of power.\n\n    See Also\n    --------\n    legadd, legsub, legmulx, legmul, legdiv\n\n    \"\"\"\n    return pu._pow(legmul, c, pow, maxpower)"
}
-/

/-- Helper function to evaluate a Legendre series at a given point -/
def legendreSeriesEval {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  sorry

/-- Raise a Legendre series to a power. 
    Returns the Legendre series `c` raised to the power `pow`. 
    The argument `c` is a sequence of coefficients ordered from low to high.
    i.e., [1,2,3] is the series P_0 + 2*P_1 + 3*P_2. -/
def legpow {n : Nat} (c : Vector Float n) (pow : Nat) (maxpower : Nat := 16) : 
    Id (Vector Float n) :=
  sorry

/-- Specification: legpow raises a Legendre series to a given power with proper bounds -/
theorem legpow_spec {n : Nat} (c : Vector Float n) (pow : Nat) (maxpower : Nat := 16) 
    (h_pow_bounds : pow ≤ maxpower) :
    ⦃⌜pow ≤ maxpower⌝⦄
    legpow c pow maxpower
    ⦃⇓result => ⌜(pow = 1 → result = c) ∧
                 (∀ x : Float, legendreSeriesEval result x = 
                   (legendreSeriesEval c x) ^ (Float.ofNat pow))⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>