import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebvander",
  "category": "Chebyshev polynomials",
  "description": "Pseudo-Vandermonde matrix of given degree.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebvander.html",
  "doc": "Pseudo-Vandermonde matrix of given degree.\n\n    Returns the pseudo-Vandermonde matrix of degree \`deg\` and sample points\n    \`x\`. The pseudo-Vandermonde matrix is defined by\n\n    .. math:: V[..., i] = T_i(x),\n\n    where \`\`0 <= i <= deg\`\`. The leading indices of \`V\` index the elements of\n    \`x\` and the last index is the degree of the Chebyshev polynomial.\n\n    If \`c\` is a 1-D array of coefficients of length \`\`n + 1\`\` and \`V\` is the\n    matrix \`\`V = chebvander(x, n)\`\`, then \`\`np.dot(V, c)\`\` and\n    \`\`chebval(x, c)\`\` are the same up to roundoff.  This equivalence is\n    useful both for least squares fitting and for the evaluation of a large\n    number of Chebyshev series of the same degree and sample points.\n\n    Parameters\n    ----------\n    x : array_like\n        Array of points. The dtype is converted to float64 or complex128\n        depending on whether any of the elements are complex. If \`x\` is\n        scalar it is converted to a 1-D array.\n    deg : int\n        Degree of the resulting matrix.\n\n    Returns\n    -------\n    vander : ndarray\n        The pseudo Vandermonde matrix. The shape of the returned matrix is\n        \`\`x.shape + (deg + 1,)\`\`, where The last index is the degree of the\n        corresponding Chebyshev polynomial.  The dtype will be the same as\n        the converted \`x\`.",
  "code": "def chebvander(x, deg):\n    \"\"\"Pseudo-Vandermonde matrix of given degree.\n\n    Returns the pseudo-Vandermonde matrix of degree \`deg\` and sample points\n    \`x\`. The pseudo-Vandermonde matrix is defined by\n\n    .. math:: V[..., i] = T_i(x),\n\n    where \`\`0 <= i <= deg\`\`. The leading indices of \`V\` index the elements of\n    \`x\` and the last index is the degree of the Chebyshev polynomial.\n\n    If \`c\` is a 1-D array of coefficients of length \`\`n + 1\`\` and \`V\` is the\n    matrix \`\`V = chebvander(x, n)\`\`, then \`\`np.dot(V, c)\`\` and\n    \`\`chebval(x, c)\`\` are the same up to roundoff.  This equivalence is\n    useful both for least squares fitting and for the evaluation of a large\n    number of Chebyshev series of the same degree and sample points.\n\n    Parameters\n    ----------\n    x : array_like\n        Array of points. The dtype is converted to float64 or complex128\n        depending on whether any of the elements are complex. If \`x\` is\n        scalar it is converted to a 1-D array.\n    deg : int\n        Degree of the resulting matrix.\n\n    Returns\n    -------\n    vander : ndarray\n        The pseudo Vandermonde matrix. The shape of the returned matrix is\n        \`\`x.shape + (deg + 1,)\`\`, where The last index is the degree of the\n        corresponding Chebyshev polynomial.  The dtype will be the same as\n        the converted \`x\`.\n\n    \"\"\"\n    ideg = pu._as_int(deg, \"deg\")\n    if ideg < 0:\n        raise ValueError(\"deg must be non-negative\")\n\n    x = np.array(x, copy=None, ndmin=1) + 0.0\n    dims = (ideg + 1,) + x.shape\n    dtyp = x.dtype\n    v = np.empty(dims, dtype=dtyp)\n    # Use forward recursion to generate the entries.\n    v[0] = x * 0 + 1\n    if ideg > 0:\n        x2 = 2 * x\n        v[1] = x\n        for i in range(2, ideg + 1):\n            v[i] = v[i - 1] * x2 - v[i - 2]\n    return np.moveaxis(v, 0, -1)"
}
-/

open Std.Do

/-- Pseudo-Vandermonde matrix of Chebyshev polynomials of given degree.
    
    Given a vector of sample points `x` and a degree `deg`, returns a matrix
    where each row corresponds to a sample point and each column contains
    the values of Chebyshev polynomials T_0, T_1, ..., T_deg evaluated at
    that point. -/
def chebvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry

/-- Specification: chebvander produces a matrix where entry (i,j) is the j-th Chebyshev 
    polynomial T_j evaluated at x[i], following the recurrence relation:
    T_0(x) = 1, T_1(x) = x, T_{k+1}(x) = 2x*T_k(x) - T_{k-1}(x) -/
theorem chebvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    chebvander x deg
    ⦃⇓V => ⌜-- T_0(x) = 1 for all x
            (∀ i : Fin n, (V.get i).get ⟨0, sorry⟩ = 1) ∧
            -- T_1(x) = x when deg ≥ 1
            (deg ≥ 1 → ∀ i : Fin n, (V.get i).get ⟨1, sorry⟩ = x.get i) ∧
            -- Recurrence relation: T_{k+1}(x) = 2x*T_k(x) - T_{k-1}(x) for k ≥ 1
            (∀ k : Nat, 1 ≤ k ∧ k < deg → 
              ∀ i : Fin n, 
                (V.get i).get ⟨k + 1, sorry⟩ = 
                  2 * (x.get i) * (V.get i).get ⟨k, sorry⟩ - 
                  (V.get i).get ⟨k - 1, sorry⟩) ∧
            -- Mathematical property: Chebyshev polynomials are bounded by 1 on [-1,1]
            (∀ i : Fin n, -1 ≤ x.get i ∧ x.get i ≤ 1 → 
              ∀ j : Fin (deg + 1), -1 ≤ (V.get i).get j ∧ (V.get i).get j ≤ 1) ∧
            -- Symmetry property: T_n(-x) = (-1)^n * T_n(x)
            (∀ i j : Fin n, x.get i = -(x.get j) → 
              ∀ k : Fin (deg + 1), 
                (V.get i).get k = (if k.val % 2 = 0 then 1 else -1) * (V.get j).get k)⌝⦄ := by
  sorry