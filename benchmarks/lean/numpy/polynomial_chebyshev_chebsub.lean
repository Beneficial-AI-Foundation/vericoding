import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebsub",
  "category": "Chebyshev polynomials",
  "description": "Subtract one Chebyshev series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebsub.html",
  "doc": "Subtract one Chebyshev series from another.\n\n    Returns the difference of two Chebyshev series `c1` - `c2`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series ``T_0 + 2*T_1 + 3*T_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Chebyshev series coefficients representing their difference.\n\n    See Also\n    --------\n    chebadd, chebmulx, chebmul, chebdiv, chebpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Chebyshev\n    series is a Chebyshev series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> C.chebsub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> C.chebsub(c2,c1) # -C.chebsub(c1,c2)\n    array([ 2.,  0., -2.])",
  "code": "def chebsub(c1, c2):\n    \"\"\"\n    Subtract one Chebyshev series from another.\n\n    Returns the difference of two Chebyshev series `c1` - `c2`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series ``T_0 + 2*T_1 + 3*T_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Chebyshev series coefficients representing their difference.\n\n    See Also\n    --------\n    chebadd, chebmulx, chebmul, chebdiv, chebpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Chebyshev\n    series is a Chebyshev series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> C.chebsub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> C.chebsub(c2,c1) # -C.chebsub(c1,c2)\n    array([ 2.,  0., -2.])\n\n    \"\"\"\n    return pu._sub(c1, c2)"
}
-/

open Std.Do

/-- Subtract one Chebyshev series from another component-wise.
    The input vectors c1 and c2 represent Chebyshev series coefficients
    ordered from lowest to highest degree term. -/
def chebsub {n : Nat} (c1 c2 : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: chebsub performs component-wise subtraction of two Chebyshev series.
    
    The specification includes:
    1. The basic property that each coefficient in the result is the difference
       of the corresponding coefficients in c1 and c2
    2. Anti-commutativity: chebsub(c1, c2) = -chebsub(c2, c1)
    3. Identity property: subtracting a series from itself yields zero
    4. Associativity with addition: (c1 - c2) + c2 = c1 -/
theorem chebsub_spec {n : Nat} (c1 c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    chebsub c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = c1.get i - c2.get i) ∧
                 (∀ i : Fin n, (chebsub c2 c1).get i = -(result.get i)) ∧
                 (∀ i : Fin n, (chebsub c1 c1).get i = 0)⌝⦄ := by
  sorry