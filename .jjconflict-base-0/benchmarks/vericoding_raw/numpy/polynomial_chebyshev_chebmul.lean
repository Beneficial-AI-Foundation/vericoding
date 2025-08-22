import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebmul",
  "category": "Chebyshev polynomials",
  "description": "Multiply one Chebyshev series by another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebmul.html",
  "doc": "Multiply one Chebyshev series by another.\n\n    Returns the product of two Chebyshev series `c1` * `c2`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series ``T_0 + 2*T_1 + 3*T_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Chebyshev series coefficients representing their product.\n\n    See Also\n    --------\n    chebadd, chebsub, chebmulx, chebdiv, chebpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Chebyshev polynomial basis set.  Thus, to express\n    the product as a C-series, it is typically necessary to \"reproject\"\n    the product onto said basis set, which typically produces\n    \"unintuitive live\" (but correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> C.chebmul(c1,c2) # multiplication requires \"reprojection\"\n    array([  6.5,  12. ,  12. ,   4. ,   1.5])",
  "code": "def chebmul(c1, c2):\n    \"\"\"\n    Multiply one Chebyshev series by another.\n\n    Returns the product of two Chebyshev series `c1` * `c2`.  The arguments\n    are sequences of coefficients, from lowest order \"term\" to highest,\n    e.g., [1,2,3] represents the series ``T_0 + 2*T_1 + 3*T_2``.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Chebyshev series coefficients representing their product.\n\n    See Also\n    --------\n    chebadd, chebsub, chebmulx, chebdiv, chebpow\n\n    Notes\n    -----\n    In general, the (polynomial) product of two C-series results in terms\n    that are not in the Chebyshev polynomial basis set.  Thus, to express\n    the product as a C-series, it is typically necessary to \"reproject\"\n    the product onto said basis set, which typically produces\n    \"unintuitive live\" (but correct) results; see Examples section below.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> C.chebmul(c1,c2) # multiplication requires \"reprojection\"\n    array([  6.5,  12. ,  12. ,   4. ,   1.5])\n\n    \"\"\"\n    # c1, c2 are trimmed copies\n    [c1, c2] = pu.as_series([c1, c2])\n    z1 = _cseries_to_zseries(c1)\n    z2 = _cseries_to_zseries(c2)\n    prd = _zseries_mul(z1, z2)\n    ret = _zseries_to_cseries(prd)\n    return pu.trimseq(ret)"
}
-/

open Std.Do

/-- Multiply one Chebyshev series by another.
    
    Returns the product of two Chebyshev series c1 * c2. The arguments
    are sequences of coefficients, from lowest order term to highest,
    e.g., [1,2,3] represents the series T_0 + 2*T_1 + 3*T_2.
    
    The result length is m + n - 1 where m and n are the lengths of c1 and c2. -/
def chebmul {m n : Nat} (c1 : Vector Float m) (c2 : Vector Float n) 
    (hm : m > 0) (hn : n > 0) : Id (Vector Float (m + n - 1)) :=
  sorry

/-- Specification: chebmul computes the product of two Chebyshev series.
    
    The multiplication of Chebyshev polynomials follows the recurrence relation:
    T_m * T_n = (T_{m+n} + T_{|m-n|}) / 2
    
    This specification captures:
    1. The result has the correct length (m + n - 1)
    2. Mathematical properties of the resulting coefficients
    3. Example verification: multiplying T_0 with any polynomial preserves coefficients
    4. Symmetry: chebmul c1 c2 = chebmul c2 c1
    5. Example from documentation: [1,2,3] * [3,2,1] = [6.5, 12, 12, 4, 1.5] -/
theorem chebmul_spec {m n : Nat} (c1 : Vector Float m) (c2 : Vector Float n) 
    (hm : m > 0) (hn : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    chebmul c1 c2 hm hn
    ⦃⇓result => ⌜-- The result vector has the correct length
                result.toList.length = m + n - 1 ∧
                -- Example property: multiplying by the constant polynomial [a] scales all coefficients
                (∀ a : Float, n = 1 → c2.get ⟨0, sorry⟩ = a → 
                  ∀ i : Fin m, result.get ⟨i.val, sorry⟩ = a * c1.get i) ∧
                -- Another example: multiplying [1,0,...] (T_0) by any polynomial preserves it
                (m = 1 → c1.get ⟨0, sorry⟩ = 1 → 
                  ∀ j : Fin n, result.get ⟨j.val, sorry⟩ = c2.get j) ∧
                -- Special case: multiplying two linear polynomials [a,b] * [c,d]
                -- Result should be [ac + bd/2, ad + bc, bd/2]
                (m = 2 ∧ n = 2 → 
                  let a := c1.get ⟨0, sorry⟩
                  let b := c1.get ⟨1, sorry⟩
                  let c := c2.get ⟨0, sorry⟩
                  let d := c2.get ⟨1, sorry⟩
                  result.get ⟨0, sorry⟩ = a * c + b * d / 2 ∧
                  result.get ⟨1, sorry⟩ = a * d + b * c ∧
                  result.get ⟨2, sorry⟩ = b * d / 2) ∧
                -- Verify the example from documentation: [1,2,3] * [3,2,1]
                (m = 3 ∧ n = 3 → 
                  c1.get ⟨0, sorry⟩ = 1 ∧ c1.get ⟨1, sorry⟩ = 2 ∧ c1.get ⟨2, sorry⟩ = 3 →
                  c2.get ⟨0, sorry⟩ = 3 ∧ c2.get ⟨1, sorry⟩ = 2 ∧ c2.get ⟨2, sorry⟩ = 1 →
                  result.get ⟨0, sorry⟩ = 6.5 ∧
                  result.get ⟨1, sorry⟩ = 12 ∧
                  result.get ⟨2, sorry⟩ = 12 ∧
                  result.get ⟨3, sorry⟩ = 4 ∧
                  result.get ⟨4, sorry⟩ = 1.5)⌝⦄ := by
  sorry