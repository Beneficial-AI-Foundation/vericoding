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

-- LLM HELPER
def sqrt (x : Float) : Float :=
  if x ≤ 0 then 0 else x.sqrt

-- LLM HELPER
def mkMatrix {n : Nat} (f : Fin n → Fin n → Float) : Vector (Vector Float n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- Return the scaled companion matrix of Legendre series coefficients.
    The companion matrix is symmetric when c is a Legendre basis polynomial,
    providing better eigenvalue estimates. -/
def legcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  let cn := c.get ⟨n + 1, by simp⟩
  mkMatrix fun i j => 
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      -- Super- and sub-diagonal elements
      let k := min i.val j.val
      let scl_k := 1.0 / sqrt (2.0 * k.toFloat + 1.0)
      let scl_k1 := 1.0 / sqrt (2.0 * (k + 1).toFloat + 1.0)
      (k + 1).toFloat * scl_k * scl_k1
    else if j.val = n then
      -- Last column adjustment
      let scl_i := 1.0 / sqrt (2.0 * i.val.toFloat + 1.0)
      let scl_n := 1.0 / sqrt (2.0 * n.toFloat + 1.0)
      let coeff := c.get ⟨i.val, by simp [Fin.val_lt_of_le]; exact Nat.le_succ_of_le (Nat.le_refl _)⟩
      -(coeff / cn) * (scl_i / scl_n) * (n.toFloat / (2.0 * n.toFloat - 1.0))
    else
      0.0

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
  simp [legcompanion, mkMatrix]
  and_iff_right.mp ⟨
    fun i j => by
      simp [Vector.get_ofFn]
      by_cases h1 : i.val + 1 = j.val ∨ j.val + 1 = i.val
      · by_cases h2 : j.val + 1 = i.val ∨ i.val + 1 = j.val
        · simp [h1, h2]
          congr 1
          rw [min_comm]
        · simp [h1, h2]
      · by_cases h2 : j.val + 1 = i.val ∨ i.val + 1 = j.val
        · simp [h1, h2]
        · by_cases h3 : j.val = n
          · by_cases h4 : i.val = n
            · simp [h3, h4]
            · simp [h1, h2, h3, h4]
          · by_cases h4 : i.val = n
            · simp [h1, h2, h3, h4]
            · simp [h1, h2, h3, h4],
    ⟨by simp [Vector.size_ofFn], 
     fun i => by simp [Vector.get_ofFn, Vector.size_ofFn]⟩
  ⟩