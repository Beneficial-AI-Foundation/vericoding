import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polysub",
  "category": "Standard polynomials",
  "description": "Subtract one polynomial from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polysub.html",
  "doc": "Subtract one polynomial from another.\n\n    Returns the difference of two polynomials `c1` - `c2`.  The arguments\n    are sequences of coefficients from lowest order term to highest, i.e.,\n    [1,2,3] represents the polynomial ``1 + 2*x + 3*x**2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of polynomial coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of coefficients representing their difference.\n\n    See Also\n    --------\n    polyadd, polymulx, polymul, polydiv, polypow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c1 = (1, 2, 3)\n    >>> c2 = (3, 2, 1)\n    >>> P.polysub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> P.polysub(c2, c1)  # -P.polysub(c1,c2)\n    array([ 2.,  0., -2.])",
  "code": "def polysub(c1, c2):\n    \"\"\"\n    Subtract one polynomial from another.\n\n    Returns the difference of two polynomials `c1` - `c2`.  The arguments\n    are sequences of coefficients from lowest order term to highest, i.e.,\n    [1,2,3] represents the polynomial ``1 + 2*x + 3*x**2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of polynomial coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of coefficients representing their difference.\n\n    See Also\n    --------\n    polyadd, polymulx, polymul, polydiv, polypow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c1 = (1, 2, 3)\n    >>> c2 = (3, 2, 1)\n    >>> P.polysub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> P.polysub(c2, c1)  # -P.polysub(c1,c2)\n    array([ 2.,  0., -2.])\n\n    \"\"\"\n    return pu._sub(c1, c2)"
}
-/

open Std.Do

/-- Subtract one polynomial from another.
    Returns the difference of two polynomials c1 - c2, where polynomials are
    represented as coefficient vectors from lowest order term to highest. -/
def polysub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  sorry

/-- Specification: polysub computes c1 - c2 element-wise, padding with zeros.
    The result has length max(n, m), and for each coefficient position i:
    - If i < min(n, m): result[i] = c1[i] - c2[i]
    - If min(n, m) ≤ i < n: result[i] = c1[i]
    - If min(n, m) ≤ i < m: result[i] = -c2[i]
    
    Additionally, polysub satisfies mathematical properties:
    - Anti-commutativity: polysub c1 c2 = -(polysub c2 c1)
    - Zero identity: polysub c 0 = c and polysub 0 c = -c -/
theorem polysub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    polysub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m),
        result.get i = 
          if h1 : i.val < n ∧ i.val < m then
            c1.get ⟨i.val, h1.1⟩ - c2.get ⟨i.val, h1.2⟩
          else if h2 : i.val < n ∧ i.val ≥ m then
            c1.get ⟨i.val, h2.1⟩
          else if h3 : i.val ≥ n ∧ i.val < m then
            -c2.get ⟨i.val, h3.2⟩
          else
            0⌝⦄ := by
  sorry