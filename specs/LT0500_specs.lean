-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legsub",
  "category": "Legendre polynomials",
  "description": "Subtract one Legendre series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legsub.html",
  "doc": "Subtract one Legendre series from another.\n\n    Returns the difference of two Legendre series \`c1\` - \`c2\`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Legendre series coefficients representing their difference.\n\n    See Also\n    --------\n    legadd, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Legendre\n    series is a Legendre series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legsub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> L.legsub(c2,c1) # -C.legsub(c1,c2)\n    array([ 2.,  0., -2.])",
  "code": "def legsub(c1, c2):\n    \"\"\"\n    Subtract one Legendre series from another.\n\n    Returns the difference of two Legendre series \`c1\` - \`c2\`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Legendre series coefficients representing their difference.\n\n    See Also\n    --------\n    legadd, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Legendre\n    series is a Legendre series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legsub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> L.legsub(c2,c1) # -C.legsub(c1,c2)\n    array([ 2.,  0., -2.])\n\n    \"\"\"\n    return pu._sub(c1, c2)"
}
-/

/-- Helper function to evaluate a Legendre series at a given point -/
def legendreSeriesValue {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  sorry

/-- Subtract one Legendre series from another.
    Returns the difference of two Legendre series c1 - c2.
    The sequences of coefficients are from lowest order term to highest,
    i.e., [1,2,3] represents the series P_0 + 2*P_1 + 3*P_2. -/
def legsub {n : Nat} (c1 c2 : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: legsub performs component-wise subtraction of Legendre series coefficients -/
theorem legsub_spec {n : Nat} (c1 c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    legsub c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = c1.get i - c2.get i) ∧
                 (∀ x : Float, legendreSeriesValue result x = 
                   legendreSeriesValue c1 x - legendreSeriesValue c2 x)⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>