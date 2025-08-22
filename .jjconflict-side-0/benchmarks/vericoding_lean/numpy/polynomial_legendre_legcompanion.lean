import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legcompanion",
  "category": "Legendre polynomials",
  "description": "Return the scaled companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legcompanion.html",
  "doc": "Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an Legendre basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Legendre series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).",
  "code": "def legcompanion(c):\n    \"\"\"Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an Legendre basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Legendre series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        raise ValueError('Series must have maximum degree of at least 1.')\n    if len(c) == 2:\n        return np.array([[-c[0] / c[1]]])\n\n    n = len(c) - 1\n    mat = np.zeros((n, n), dtype=c.dtype)\n    scl = 1. / np.sqrt(2 * np.arange(n) + 1)\n    top = mat.reshape(-1)[1::n + 1]\n    bot = mat.reshape(-1)[n::n + 1]\n    top[...] = np.arange(1, n) * scl[:n - 1] * scl[1:n]\n    bot[...] = top\n    mat[:, -1] -= (c[:-1] / c[-1]) * (scl / scl[-1]) * (n / (2 * n - 1))\n    return mat"
}
-/

/-- Return the scaled companion matrix of Legendre series coefficients.
    The companion matrix is symmetric when c is a Legendre basis polynomial,
    providing better eigenvalue estimates. -/
def legcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry

/-- Specification: legcompanion returns a symmetric companion matrix of appropriate dimensions -/
theorem legcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get ⟨n + 1, by simp⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by simp⟩ ≠ 0⌝⦄
    legcompanion c
    ⦃⇓result => ⌜
      (∀ i j : Fin (n + 1), (result.get i).get j = (result.get j).get i) ∧
      (result.size = n + 1) ∧
      (∀ i : Fin (n + 1), (result.get i).size = n + 1)
    ⌝⦄ := by
  sorry