import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.vander",
  "category": "Building matrices",
  "description": "Generate a Vandermonde matrix",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.vander.html",
  "doc": "\nGenerate a Vandermonde matrix.\n\nParameters\n----------\nx : array_like\n    1-D input array.\nN : int, optional\n    Number of columns in the output. If N is not specified, a square array is returned (N = len(x)).\nincreasing : bool, optional\n    Order of the powers of the columns. If True, the powers increase from left to right, \n    if False (the default) they are reversed.\n\nReturns\n-------\nout : ndarray\n    Vandermonde matrix. If increasing is False, the first column is x^(N-1), the second x^(N-2) \n    and so forth. If increasing is True, the columns are x^0, x^1, ..., x^(N-1).\n\nExamples\n--------\n>>> x = np.array([1, 2, 3, 5])\n>>> N = 3\n>>> np.vander(x, N)\narray([[ 1,  1,  1],\n       [ 4,  2,  1],\n       [ 9,  3,  1],\n       [25,  5,  1]])\n\n>>> np.column_stack([x**(N-1-i) for i in range(N)])\narray([[ 1,  1,  1],\n       [ 4,  2,  1],\n       [ 9,  3,  1],\n       [25,  5,  1]])\n\n>>> x = np.array([1, 2, 3, 5])\n>>> np.vander(x)\narray([[  1,   1,   1,   1],\n       [  8,   4,   2,   1],\n       [ 27,   9,   3,   1],\n       [125,  25,   5,   1]])\n>>> np.vander(x, increasing=True)\narray([[  1,   1,   1,   1],\n       [  1,   2,   4,   8],\n       [  1,   3,   9,  27],\n       [  1,   5,  25, 125]])\n",
  "code": "@array_function_dispatch(_vander_dispatcher)\ndef vander(x, N=None, increasing=False):\n    \"\"\"\n    Generate a Vandermonde matrix.\n\n    The columns of the output matrix are powers of the input vector. The\n    order of the powers is determined by the \`increasing\` boolean argument.\n    Specifically, when \`increasing\` is False, the \`i\`-th output column is\n    the input vector raised element-wise to the power of \`\`N - i - 1\`\`. Such\n    a matrix with a geometric progression in each row is named for Alexandre-\n    Theophile Vandermonde.\n    \"\"\"\n    x = asarray(x)\n    if x.ndim != 1:\n        raise ValueError(\"x must be a one-dimensional array or sequence.\")\n    if N is None:\n        N = len(x)\n\n    v = empty((len(x), N), dtype=promote_types(x.dtype, int))\n    tmp = v[:, ::-1] if not increasing else v\n\n    if N > 0:\n        tmp[:, 0] = 1\n    if N > 1:\n        tmp[:, 1:] = x[:, None]\n        multiply.accumulate(tmp[:, 1:], out=tmp[:, 1:], axis=1)\n\n    return v",
  "signature": "numpy.vander(x, N=None, increasing=False)"
}
-/

open Std.Do

/-- Generate a Vandermonde matrix with decreasing powers (default behavior).
    The Vandermonde matrix is a matrix with terms of a geometric progression in each row.
    For a 1D input vector x of length n and specified number of columns m,
    the output is an n×m matrix where entry (i,j) = x[i]^(m-1-j) -/
def vander {n m : Nat} (x : Vector Float n) : Id (Vector (Vector Float m) n) :=
  sorry

/-- Specification: vander generates a Vandermonde matrix where each row contains
    powers of the corresponding element from the input vector.
    In the default decreasing mode, column j contains x^(m-1-j) for each element x.
    This means the first column has the highest powers and the last column has x^0 = 1. -/
theorem vander_spec {n m : Nat} (x : Vector Float n) (h_m_pos : m > 0) :
    ⦃⌜m > 0⌝⦄
    vander x
    ⦃⇓result => ⌜∀ (i : Fin n) (j : Fin m), 
                  (result.get i).get j = (x.get i) ^ ((m - 1 - j.val).toFloat)⌝⦄ := by
  sorry