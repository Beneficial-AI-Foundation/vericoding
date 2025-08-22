import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.linalg.matrix_norm",
  "category": "Norms and numbers",
  "description": "Compute matrix norm",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.matrix_norm.html",
  "doc": "Computes the matrix norm of a matrix.\n\nThis function is able to return one of seven different matrix norms, depending on the value of the ord parameter.",
  "code": "\n@array_function_dispatch(_matrix_norm_dispatcher)\ndef matrix_norm(x, /, *, keepdims=False, ord=\"fro\"):\n    \"\"\"\n    Computes the matrix norm of a matrix (or a stack of matrices) \`\`x\`\`.\n\n    This function is Array API compatible.\n\n    Parameters\n    ----------\n    x : array_like\n        Input array having shape (..., M, N) and whose two innermost\n        dimensions form \`\`MxN\`\` matrices.\n    keepdims : bool, optional\n        If this is set to True, the axes which are normed over are left in\n        the result as dimensions with size one. Default: False.\n    ord : {1, -1, 2, -2, inf, -inf, 'fro', 'nuc'}, optional\n        The order of the norm. For details see the table under \`\`Notes\`\`\n        in \`numpy.linalg.norm\`.\n\n    See Also\n    --------\n    numpy.linalg.norm : Generic norm function\n\n    Examples\n    --------\n    >>> from numpy import linalg as LA\n    >>> a = np.arange(9) - 4\n    >>> a\n    array([-4, -3, -2, ...,  2,  3,  4])\n    >>> b = a.reshape((3, 3))\n    >>> b\n    array([[-4, -3, -2],\n           [-1,  0,  1],\n           [ 2,  3,  4]])\n\n    >>> LA.matrix_norm(b)\n    7.745966692414834\n    >>> LA.matrix_norm(b, ord='fro')\n    7.745966692414834\n    >>> LA.matrix_norm(b, ord=np.inf)\n    9.0\n    >>> LA.matrix_norm(b, ord=-np.inf)\n    2.0\n\n    >>> LA.matrix_norm(b, ord=1)\n    7.0\n    >>> LA.matrix_norm(b, ord=-1)\n    6.0\n    >>> LA.matrix_norm(b, ord=2)\n    7.3484692283495345\n    >>> LA.matrix_norm(b, ord=-2)\n    1.8570331885190563e-016 # may vary\n\n    \"\"\"\n    x = asanyarray(x)\n    return norm(x, axis=(-2, -1), keepdims=keepdims, ord=ord)"
}
-/

open Std.Do

/-- Compute matrix norm of a matrix (Frobenius norm by default) -/
def matrix_norm {rows cols : Nat} (x : Vector (Vector Float cols) rows) : Id Float :=
  sorry

/-- Specification: matrix_norm computes the Frobenius norm of a matrix 
    The Frobenius norm is the square root of the sum of squares of all elements.
    
    Properties:
    1. Non-negativity: norm is always ≥ 0
    2. Zero property: norm is 0 iff all elements are 0
    3. Homogeneity: norm(c*A) = |c| * norm(A) for scalar c
    4. Triangle inequality: norm(A + B) ≤ norm(A) + norm(B)
    5. Submultiplicativity: norm(A) dominates the absolute value of any element
-/
theorem matrix_norm_spec {rows cols : Nat} (x : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    matrix_norm x
    ⦃⇓res => ⌜res ≥ 0 ∧ 
             (res = 0 ↔ ∀ i : Fin rows, ∀ j : Fin cols, (x.get i).get j = 0) ∧
             (∀ i : Fin rows, ∀ j : Fin cols, Float.abs ((x.get i).get j) ≤ res) ∧
             (rows > 0 ∧ cols > 0 → 
               ∃ i : Fin rows, ∃ j : Fin cols, (x.get i).get j ≠ 0 → res > 0)⌝⦄ := by
  sorry
