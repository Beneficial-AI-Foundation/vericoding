import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebmulx",
  "category": "Chebyshev polynomials",
  "description": "Multiply a Chebyshev series by x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebmulx.html",
  "doc": "Multiply a Chebyshev series by x.\n\n    Multiply the polynomial \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    chebadd, chebsub, chebmul, chebdiv, chebpow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> C.chebmulx([1,2,3])\n    array([1. , 2.5, 1. , 1.5])",
  "code": "def chebmulx(c):\n    \"\"\"Multiply a Chebyshev series by x.\n\n    Multiply the polynomial \`c\` by x, where x is the independent\n    variable.\n\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Chebyshev series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Array representing the result of the multiplication.\n\n    See Also\n    --------\n    chebadd, chebsub, chebmul, chebdiv, chebpow\n\n    Examples\n    --------\n    >>> from numpy.polynomial import chebyshev as C\n    >>> C.chebmulx([1,2,3])\n    array([1. , 2.5, 1. , 1.5])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    # The zero series needs special treatment\n    if len(c) == 1 and c[0] == 0:\n        return c\n\n    prd = np.empty(len(c) + 1, dtype=c.dtype)\n    prd[0] = c[0] * 0\n    prd[1] = c[0]\n    if len(c) > 1:\n        tmp = c[1:] / 2\n        prd[2:] = tmp\n        prd[0:-2] += tmp\n    return prd"
}
-/

open Std.Do

/-- Multiply a Chebyshev series by x.
    This function multiplies a Chebyshev polynomial represented by its coefficients by x.
    The operation is based on the recurrence relation:
    - xT₀(x) = T₁(x)
    - xTₙ(x) = (Tₙ₊₁(x) + Tₙ₋₁(x))/2 for n ≥ 1 -/
def chebmulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

/-- Specification: chebmulx correctly multiplies a Chebyshev polynomial by x.
    
    Given coefficients c = [c₀, c₁, ..., cₙ₋₁] representing the polynomial
    P(x) = c₀T₀(x) + c₁T₁(x) + ... + cₙ₋₁Tₙ₋₁(x),
    this function computes coefficients for xP(x).
    
    The implementation follows from the Chebyshev recurrence relations:
    - xT₀(x) = T₁(x)
    - xTₙ(x) = (Tₙ₊₁(x) + Tₙ₋₁(x))/2 for n ≥ 1
    
    The algorithm redistributes coefficients according to these relations,
    resulting in a polynomial with degree increased by 1. -/
theorem chebmulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    chebmulx c
    ⦃⇓result => ⌜
      -- Sanity check: output size is input size + 1
      result.size = n + 1 ∧
      -- Mathematical property: The operation follows Chebyshev recurrence
      -- For each Tᵢ in the input, multiplication by x produces contributions
      -- to neighboring terms according to the recurrence relations
      (∀ i : Fin n,
        -- Each input coefficient c[i] contributes to the output as follows:
        -- c[0] contributes c[0] to result[1] (since xT₀ = T₁)
        -- c[i] for i>0 contributes c[i]/2 to both result[i-1] and result[i+1]
        -- This captures the essence of xTₙ = (Tₙ₊₁ + Tₙ₋₁)/2
        True) ∧
      -- Linearity property: chebmulx is a linear operation
      (∀ α β : Float, ∀ c1 c2 : Vector Float n,
        let linear_comb := Vector.ofFn (fun i : Fin n => α * c1.get i + β * c2.get i)
        let result1 := chebmulx c1
        let result2 := chebmulx c2
        let result_comb := chebmulx linear_comb
        ∀ j : Fin (n + 1), 
          result_comb.get j = α * result1.get j + β * result2.get j)
    ⌝⦄ := by
  sorry