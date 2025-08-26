import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagcompanion",
  "category": "Laguerre polynomials",
  "description": "Return the companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagcompanion.html",
  "doc": "Return the companion matrix of c.\n\n    The usual companion matrix of the Laguerre polynomials is already\n    symmetric when \`c\` is a basis Laguerre polynomial, so no scaling is\n    applied.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Laguerre series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagcompanion\n    >>> lagcompanion([1, 2, 3])\n    array([[ 1.        , -0.33333333],\n           [-1.        ,  4.33333333]])",
  "code": "def lagcompanion(c):\n    \"\"\"\n    Return the companion matrix of c.\n\n    The usual companion matrix of the Laguerre polynomials is already\n    symmetric when \`c\` is a basis Laguerre polynomial, so no scaling is\n    applied.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of Laguerre series coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagcompanion\n    >>> lagcompanion([1, 2, 3])\n    array([[ 1.        , -0.33333333],\n           [-1.        ,  4.33333333]])\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        raise ValueError('Series must have maximum degree of at least 1.')\n    if len(c) == 2:\n        return np.array([[1 + c[0] / c[1]]])\n\n    n = len(c) - 1\n    mat = np.zeros((n, n), dtype=c.dtype)\n    top = mat.reshape(-1)[1::n + 1]\n    mid = mat.reshape(-1)[0::n + 1]\n    bot = mat.reshape(-1)[n::n + 1]\n    top[...] = -np.arange(1, n)\n    mid[...] = 2. * np.arange(n) + 1.\n    bot[...] = top\n    mat[:, -1] += (c[:-1] / c[-1]) * n\n    return mat"
}
-/

/-- Returns the companion matrix of Laguerre polynomial coefficients.
    The companion matrix is a square matrix of size (deg, deg) where deg = c.size - 1.
    For coefficients [c₀, c₁, ..., cₙ], the companion matrix has specific structure
    for Laguerre polynomials with diagonal elements 2*i + 1 and off-diagonal elements. -/
def lagcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry

/-- Specification: lagcompanion returns the companion matrix of Laguerre polynomial coefficients.
    The companion matrix is symmetric for Laguerre polynomials and has dimension (deg, deg)
    where deg = c.size - 1. The matrix structure follows the Laguerre polynomial recurrence relation. -/
theorem lagcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get (Fin.last (n + 1)) ≠ 0) :
    ⦃⌜c.get (Fin.last (n + 1)) ≠ 0⌝⦄
    lagcompanion c
    ⦃⇓mat => ⌜-- Matrix has correct dimensions
             mat.size = n + 1 ∧ 
             (∀ i : Fin (n + 1), (mat.get i).size = n + 1) ∧
             -- Diagonal elements follow pattern: 2*i + 1  
             (∀ i : Fin (n + 1), (mat.get i).get i = 2 * Float.ofNat i.val + 1) ∧
             -- Off-diagonal elements for tridiagonal structure
             (∀ i : Fin n, (mat.get (i.castSucc)).get (i.succ) = -(Float.ofNat i.val + 1)) ∧
             (∀ i : Fin n, (mat.get (i.succ)).get (i.castSucc) = -(Float.ofNat i.val + 1))⌝⦄ := by
  sorry