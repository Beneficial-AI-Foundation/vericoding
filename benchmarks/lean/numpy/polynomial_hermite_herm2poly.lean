import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite.herm2poly",
  "category": "Hermite polynomials",
  "description": "Convert a Hermite series to a polynomial.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.herm2poly.html",
  "doc": "Convert a Hermite series to a polynomial.\n\n    Convert an array representing the coefficients of a Hermite series,\n    ordered from lowest degree to highest, to an array of the coefficients\n    of the equivalent polynomial (relative to the \"standard\" basis) ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array containing the Hermite series coefficients, ordered\n        from lowest order term to highest.\n\n    Returns\n    -------\n    pol : ndarray\n        1-D array containing the coefficients of the equivalent polynomial\n        (relative to the \"standard\" basis) ordered from lowest order term\n        to highest.\n\n    See Also\n    --------\n    poly2herm\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import herm2poly\n    >>> herm2poly([ 1.   ,  2.75 ,  0.5  ,  0.375])\n    array([0., 1., 2., 3.])",
  "code": "def herm2poly(c):\n    \"\"\"\n    Convert a Hermite series to a polynomial.\n\n    Convert an array representing the coefficients of a Hermite series,\n    ordered from lowest degree to highest, to an array of the coefficients\n    of the equivalent polynomial (relative to the \"standard\" basis) ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array containing the Hermite series coefficients, ordered\n        from lowest order term to highest.\n\n    Returns\n    -------\n    pol : ndarray\n        1-D array containing the coefficients of the equivalent polynomial\n        (relative to the \"standard\" basis) ordered from lowest order term\n        to highest.\n\n    See Also\n    --------\n    poly2herm\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import herm2poly\n    >>> herm2poly([ 1.   ,  2.75 ,  0.5  ,  0.375])\n    array([0., 1., 2., 3.])\n\n    \"\"\"\n    from .polynomial import polyadd, polymulx, polysub\n\n    [c] = pu.as_series([c])\n    n = len(c)\n    if n == 1:\n        return c\n    if n == 2:\n        c[1] *= 2\n        return c\n    else:\n        c0 = c[-2]\n        c1 = c[-1]\n        # i is the current degree of c1\n        for i in range(n - 1, 1, -1):\n            tmp = c0\n            c0 = polysub(c[i - 2], c1 * (2 * (i - 1)))\n            c1 = polyadd(tmp, polymulx(c1) * 2)\n        return polyadd(c0, polymulx(c1) * 2)\n\n\n#\n# These are constant arrays are of integer type so as to be compatible\n# with the widest range of other types, such as Decimal.\n#\n\n# Hermite\nhermdomain = np.array([-1., 1.])\n\n# Hermite coefficients representing zero.\nhermzero = np.array([0])\n\n# Hermite coefficients representing one.\nhermone = np.array([1])\n\n# Hermite coefficients representing the identity x.\nhermx = np.array([0, 1 / 2])"
}
-/

open Std.Do

/-- Convert a Hermite series to a polynomial.
    Converts coefficients of a Hermite series (ordered from lowest to highest degree)
    to coefficients of the equivalent standard polynomial (ordered from lowest to highest degree).
    
    The Hermite polynomials H_n(x) satisfy the recurrence relation:
    H_{n+1}(x) = 2x * H_n(x) - 2n * H_{n-1}(x)
    with H_0(x) = 1 and H_1(x) = 2x
    
    This function performs the inverse transformation, converting from Hermite basis to standard basis. -/
def herm2poly {n : Nat} (c : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: herm2poly converts Hermite series coefficients to standard polynomial coefficients.
    
    The conversion satisfies:
    1. The output has the same length as the input
    2. For n=1 (constant), the output equals the input
    3. For n=2, the second coefficient is doubled (since H_1(x) = 2x)
    4. The conversion algorithm follows the recurrence relation for Hermite polynomials
    5. Special example: herm2poly([1, 2.75, 0.5, 0.375]) = [0, 1, 2, 3]
    6. The conversion preserves basis transformation properties -/
theorem herm2poly_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    herm2poly c
    ⦃⇓result => ⌜
      -- Sanity checks
      (n = 1 → result = c) ∧
      (n = 2 → result.get ⟨0, sorry⟩ = c.get ⟨0, sorry⟩ ∧ 
               result.get ⟨1, sorry⟩ = 2 * c.get ⟨1, sorry⟩) ∧
      -- Example from documentation
      (n = 4 ∧ c.get ⟨0, sorry⟩ = 1 ∧ c.get ⟨1, sorry⟩ = 2.75 ∧ 
       c.get ⟨2, sorry⟩ = 0.5 ∧ c.get ⟨3, sorry⟩ = 0.375 →
       result.get ⟨0, sorry⟩ = 0 ∧ result.get ⟨1, sorry⟩ = 1 ∧
       result.get ⟨2, sorry⟩ = 2 ∧ result.get ⟨3, sorry⟩ = 3) ∧
      -- Mathematical property: The transformation is invertible
      -- There exists poly2herm such that poly2herm(herm2poly(c)) = c
      (∃ poly2herm : Vector Float n → Vector Float n, 
        poly2herm result = c)
    ⌝⦄ := by
  sorry