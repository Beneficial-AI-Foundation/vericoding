import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite.hermcompanion",
  "category": "Hermite polynomials",
  "description": "Return the scaled companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermcompanion.html",
  "doc": "Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an Hermite basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermcompanion\n    >>> hermcompanion([1, 0, 1])\n    array([[0.        , 0.35355339],\n           [0.70710678, 0.        ]])",
  "code": "def hermcompanion(c):\n    \"\"\"Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an Hermite basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Hermite series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermcompanion\n    >>> hermcompanion([1, 0, 1])\n    array([[0.        , 0.35355339],\n           [0.70710678, 0.        ]])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        raise ValueError('Series must have maximum degree of at least 1.')\n    if len(c) == 2:\n        return np.array([[-.5 * c[0] / c[1]]])\n\n    n = len(c) - 1\n    mat = np.zeros((n, n), dtype=c.dtype)\n    scl = np.hstack((1., 1. / np.sqrt(2. * np.arange(n - 1, 0, -1))))\n    scl = np.multiply.accumulate(scl)[::-1]\n    top = mat.reshape(-1)[1::n + 1]\n    bot = mat.reshape(-1)[n::n + 1]\n    top[...] = np.sqrt(.5 * np.arange(1, n))\n    bot[...] = top\n    mat[:, -1] -= scl * c[:-1] / (2.0 * c[-1])\n    return mat"
}
-/

open Std.Do

/-- Return the scaled companion matrix of Hermite polynomial coefficients.
    The companion matrix is symmetric when c represents a Hermite basis polynomial. -/
def hermcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry

/-- Specification: hermcompanion produces a scaled companion matrix with specific properties.
    For a coefficient vector of length n+2, the result is an (n+1)×(n+1) matrix where:
    1. The super-diagonal and sub-diagonal contain sqrt(k/2) for k = 1 to n
    2. The last column is adjusted by scaled coefficients
    3. The matrix is symmetric when c represents a Hermite basis polynomial -/
theorem hermcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get ⟨n + 1, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by omega⟩ ≠ 0⌝⦄
    hermcompanion c
    ⦃⇓mat => ⌜
      -- The matrix has the correct diagonal structure
      (∀ k : Fin n, (mat.get ⟨k.val, by omega⟩).get ⟨k.val + 1, by omega⟩ = 
        Float.sqrt (0.5 * Float.ofNat (k.val + 1))) ∧
      (∀ k : Fin n, (mat.get ⟨k.val + 1, by omega⟩).get ⟨k.val, by omega⟩ = 
        Float.sqrt (0.5 * Float.ofNat (k.val + 1))) ∧
      -- All other entries except last column are zero
      (∀ i j : Fin (n + 1), 
        (i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val ∧ j.val ≠ n) → 
        (mat.get i).get j = 0) ∧
      -- Last column has special scaling based on coefficients
      (∀ i : Fin (n + 1), 
        ∃ scale : Float, (mat.get i).get ⟨n, by omega⟩ = 
          if i.val + 1 = n ∨ i.val = n + 1 then
            Float.sqrt (0.5 * Float.ofNat n) - scale * c.get ⟨i.val, by omega⟩ / (2.0 * c.get ⟨n + 1, by omega⟩)
          else
            - scale * c.get ⟨i.val, by omega⟩ / (2.0 * c.get ⟨n + 1, by omega⟩))
    ⌝⦄ := by
  sorry