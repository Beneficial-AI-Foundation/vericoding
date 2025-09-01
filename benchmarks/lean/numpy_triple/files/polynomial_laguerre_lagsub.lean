/- 
{
  "name": "numpy.polynomial.laguerre.lagsub",
  "category": "Laguerre polynomials",
  "description": "Subtract one Laguerre series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagsub.html",
  "doc": "Subtract one Laguerre series from another.\n\n    Returns the difference of two Laguerre series \`c1\` - \`c2\`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Laguerre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Laguerre series coefficients representing their difference.\n\n    See Also\n    --------\n    lagadd, lagmulx, lagmul, lagdiv, lagpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Laguerre\n    series is a Laguerre series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagsub\n    >>> lagsub([1, 2, 3, 4], [1, 2, 3])\n    array([0.,  0.,  0.,  4.])",
}
-/

/-  Subtract one Laguerre series from another.

    Returns the difference of two Laguerre series `c1` - `c2`.  The
    sequences of coefficients are from lowest order term to highest, i.e.,
    [1,2,3] represents the series ``P_0 + 2*P_1 + 3*P_2``.
-/

/-  Specification: lagsub subtracts two Laguerre series component-wise -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def lagsub {n : Nat} (c1 c2 : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem lagsub_spec {n : Nat} (c1 c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    lagsub c1 c2
    ⦃⇓result => ⌜
      -- Component-wise subtraction: result[i] = c1[i] - c2[i]
      ∀ i : Fin n, result.get i = c1.get i - c2.get i ∧
      -- The difference of two Laguerre series is a Laguerre series
      -- This operation is linear and preserves the Laguerre basis
      -- Mathematical property: if c1 represents polynomial p(x) and c2 represents q(x),
      -- then result represents polynomial (p - q)(x) in the Laguerre basis
      True -- Placeholder for more complex Laguerre polynomial properties
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
