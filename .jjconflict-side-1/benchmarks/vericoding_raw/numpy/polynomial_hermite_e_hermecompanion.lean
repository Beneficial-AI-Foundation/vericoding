import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite_e.hermecompanion",
  "category": "HermiteE polynomials",
  "description": "Return the scaled companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermecompanion.html",
  "doc": "Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an HermiteE basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of HermiteE series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).",
  "code": "def hermecompanion(c):\n    \"\"\"\n    Return the scaled companion matrix of c.\n\n    The basis polynomials are scaled so that the companion matrix is\n    symmetric when \`c\` is an HermiteE basis polynomial. This provides\n    better eigenvalue estimates than the unscaled case and for basis\n    polynomials the eigenvalues are guaranteed to be real if\n    \`numpy.linalg.eigvalsh\` is used to obtain them.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of HermiteE series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Scaled companion matrix of dimensions (deg, deg).\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        raise ValueError('Series must have maximum degree of at least 1.')\n    if len(c) == 2:\n        return np.array([[-c[0] / c[1]]])\n\n    n = len(c) - 1\n    mat = np.zeros((n, n), dtype=c.dtype)\n    scl = np.hstack((1., 1. / np.sqrt(np.arange(n - 1, 0, -1))))\n    scl = np.multiply.accumulate(scl)[::-1]\n    top = mat.reshape(-1)[1::n + 1]\n    bot = mat.reshape(-1)[n::n + 1]\n    top[...] = np.sqrt(np.arange(1, n))\n    bot[...] = top\n    mat[:, -1] -= scl * c[:-1] / c[-1]\n    return mat"
}
-/

open Std.Do

/-- Return the scaled companion matrix of HermiteE series coefficients.
    The companion matrix is scaled for better eigenvalue estimates and
    symmetry properties when used with HermiteE basis polynomials. -/
def hermecompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry

/-- Specification: hermecompanion returns a scaled companion matrix with specific properties -/
theorem hermecompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_last_nonzero : c.get ⟨n + 1, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by omega⟩ ≠ 0⌝⦄
    hermecompanion c
    ⦃⇓mat => ⌜
      -- Matrix is symmetric (superdiagonal equals subdiagonal)
      (∀ i : Fin n, (mat.get ⟨i.val, by omega⟩).get ⟨i.val + 1, by omega⟩ = 
        (mat.get ⟨i.val + 1, by omega⟩).get ⟨i.val, by omega⟩) ∧
      -- Superdiagonal elements are sqrt(i+1) for i = 0 to n-1
      (∀ i : Fin n, (mat.get ⟨i.val, by omega⟩).get ⟨i.val + 1, by omega⟩ = 
        Float.sqrt (Float.ofNat (i.val + 1))) ∧
      -- Last column contains scaled coefficients except for the last element
      (∀ i : Fin (n + 1), (mat.get i).get ⟨n, by omega⟩ = 
        -(c.get ⟨i.val, by omega⟩ / c.get ⟨n + 1, by omega⟩)) ∧
      -- All other elements are zero (excluding superdiagonal, subdiagonal, and last column)
      (∀ i j : Fin (n + 1), j.val ≠ i.val + 1 ∧ j.val ≠ n ∧ i.val ≠ j.val + 1 → 
        (mat.get i).get j = (0 : Float))
    ⌝⦄ := by
  sorry