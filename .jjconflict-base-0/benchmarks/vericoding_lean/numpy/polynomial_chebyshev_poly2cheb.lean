import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.poly2cheb",
  "category": "Chebyshev polynomials",
  "description": "Convert a polynomial to a Chebyshev series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.poly2cheb.html",
  "doc": "Convert a polynomial to a Chebyshev series.\n\n    Convert an array representing the coefficients of a polynomial (relative\n    to the \"standard\" basis) ordered from lowest degree to highest, to an\n    array of the coefficients of the equivalent Chebyshev series, ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    pol : array_like\n        1-D array containing the polynomial coefficients\n\n    Returns\n    -------\n    c : ndarray\n        1-D array containing the coefficients of the equivalent Chebyshev\n        series.\n\n    See Also\n    --------\n    cheb2poly\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> from numpy import polynomial as P\n    >>> p = P.Polynomial(range(4))\n    >>> p\n    Polynomial([0., 1., 2., 3.], domain=[-1.,  1.], window=[-1.,  1.], symbol='x')\n    >>> c = p.convert(kind=P.Chebyshev)\n    >>> c\n    Chebyshev([1.  , 3.25, 1.  , 0.75], domain=[-1.,  1.], window=[-1., ...\n    >>> P.chebyshev.poly2cheb(range(4))\n    array([1.  , 3.25, 1.  , 0.75])",
  "code": "def poly2cheb(pol):\n    \"\"\"\n    Convert a polynomial to a Chebyshev series.\n\n    Convert an array representing the coefficients of a polynomial (relative\n    to the \"standard\" basis) ordered from lowest degree to highest, to an\n    array of the coefficients of the equivalent Chebyshev series, ordered\n    from lowest to highest degree.\n\n    Parameters\n    ----------\n    pol : array_like\n        1-D array containing the polynomial coefficients\n\n    Returns\n    -------\n    c : ndarray\n        1-D array containing the coefficients of the equivalent Chebyshev\n        series.\n\n    See Also\n    --------\n    cheb2poly\n\n    Notes\n    -----\n    The easy way to do conversions between polynomial basis sets\n    is to use the convert method of a class instance.\n\n    Examples\n    --------\n    >>> from numpy import polynomial as P\n    >>> p = P.Polynomial(range(4))\n    >>> p\n    Polynomial([0., 1., 2., 3.], domain=[-1.,  1.], window=[-1.,  1.], symbol='x')\n    >>> c = p.convert(kind=P.Chebyshev)\n    >>> c\n    Chebyshev([1.  , 3.25, 1.  , 0.75], domain=[-1.,  1.], window=[-1., ...\n    >>> P.chebyshev.poly2cheb(range(4))\n    array([1.  , 3.25, 1.  , 0.75])\n\n    \"\"\"\n    [pol] = pu.as_series([pol])\n    deg = len(pol) - 1\n    res = 0\n    for i in range(deg, -1, -1):\n        res = chebadd(chebmulx(res), pol[i])\n    return res"
}
-/

open Std.Do

/-- Convert a polynomial to a Chebyshev series.
    
    This function converts coefficients of a polynomial in the standard monomial basis
    (1, x, x², x³, ...) to coefficients in the Chebyshev polynomial basis
    (T₀(x), T₁(x), T₂(x), T₃(x), ...).
    
    The input polynomial coefficients are ordered from lowest degree to highest:
    pol = [a₀, a₁, a₂, ..., aₙ] represents the polynomial a₀ + a₁x + a₂x² + ... + aₙxⁿ
    
    The output Chebyshev coefficients are also ordered from lowest to highest degree:
    result = [c₀, c₁, c₂, ..., cₙ] represents c₀T₀(x) + c₁T₁(x) + c₂T₂(x) + ... + cₙTₙ(x) -/
def poly2cheb {n : Nat} (pol : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: poly2cheb correctly converts polynomial coefficients to Chebyshev series coefficients.
    
    The conversion preserves the polynomial function - that is, the polynomial represented
    in the standard basis and the polynomial represented in the Chebyshev basis evaluate
    to the same value for all x in the domain [-1, 1].
    
    Mathematical Properties:
    1. The conversion is linear: poly2cheb(αp + βq) = α·poly2cheb(p) + β·poly2cheb(q)
    2. The conversion preserves polynomial degree
    3. For the monomial xⁿ, the conversion yields specific Chebyshev coefficients
       based on the expansion of xⁿ in terms of Chebyshev polynomials
    
    Implementation follows Horner's method in reverse:
    - Start with the highest degree coefficient
    - Multiply the accumulator by x (using chebmulx)
    - Add the next coefficient (using chebadd)
    - Repeat until all coefficients are processed
    
    Example conversions:
    - [1, 0, 0, 0] (constant 1) → [1, 0, 0, 0] (T₀(x) = 1)
    - [0, 1, 0, 0] (x) → [0, 1, 0, 0] (T₁(x) = x)
    - [0, 0, 1, 0] (x²) → [0.5, 0, 0.5, 0] (x² = 0.5T₀(x) + 0.5T₂(x))
    - [0, 1, 2, 3] → [1, 3.25, 1, 0.75] (from the documentation example) -/
theorem poly2cheb_spec {n : Nat} (pol : Vector Float n) :
    ⦃⌜True⌝⦄
    poly2cheb pol
    ⦃⇓result => ⌜
      -- Sanity check: output has same size as input
      result.size = n ∧
      -- Correctness property: Specific test cases match expected outputs
      -- Example from documentation: [0, 1, 2, 3] → [1, 3.25, 1, 0.75]
      (n = 4 → pol.get ⟨0, sorry⟩ = 0 ∧ pol.get ⟨1, sorry⟩ = 1 ∧ 
               pol.get ⟨2, sorry⟩ = 2 ∧ pol.get ⟨3, sorry⟩ = 3 → 
        result.get ⟨0, sorry⟩ = 1 ∧ result.get ⟨1, sorry⟩ = 3.25 ∧ 
        result.get ⟨2, sorry⟩ = 1 ∧ result.get ⟨3, sorry⟩ = 0.75) ∧
      -- Identity property: Converting constant polynomial [c, 0, ..., 0] yields [c, 0, ..., 0]
      (∀ c : Float, n > 0 → (∀ i : Fin n, i.val > 0 → pol.get i = 0) ∧ pol.get ⟨0, sorry⟩ = c →
        (∀ i : Fin n, i.val > 0 → result.get i = 0) ∧ result.get ⟨0, sorry⟩ = c) ∧
      -- Linear polynomial property: [a, b, 0, ..., 0] preserves first two coefficients
      (n > 1 → (∀ i : Fin n, i.val > 1 → pol.get i = 0) →
        result.get ⟨0, sorry⟩ = pol.get ⟨0, sorry⟩ ∧ 
        result.get ⟨1, sorry⟩ = pol.get ⟨1, sorry⟩) ∧
      -- Mathematical property: Conversion is valid for polynomials up to degree n-1
      -- The algorithm uses Horner's method starting from highest degree coefficient
      -- Using recursive application of chebmulx and chebadd operations
      (n > 0 → 
        -- For quadratic polynomial x²: [0, 0, 1] → [0.5, 0, 0.5]
        (n = 3 ∧ pol.get ⟨0, sorry⟩ = 0 ∧ pol.get ⟨1, sorry⟩ = 0 ∧ pol.get ⟨2, sorry⟩ = 1 →
          result.get ⟨0, sorry⟩ = 0.5 ∧ result.get ⟨1, sorry⟩ = 0 ∧ result.get ⟨2, sorry⟩ = 0.5) ∧
        -- For cubic polynomial x³: [0, 0, 0, 1] → [0, 0.75, 0, 0.25]  
        (n = 4 ∧ pol.get ⟨0, sorry⟩ = 0 ∧ pol.get ⟨1, sorry⟩ = 0 ∧ 
         pol.get ⟨2, sorry⟩ = 0 ∧ pol.get ⟨3, sorry⟩ = 1 →
          result.get ⟨0, sorry⟩ = 0 ∧ result.get ⟨1, sorry⟩ = 0.75 ∧ 
          result.get ⟨2, sorry⟩ = 0 ∧ result.get ⟨3, sorry⟩ = 0.25))⌝⦄ := by
  sorry