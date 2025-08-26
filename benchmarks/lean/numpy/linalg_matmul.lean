import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.linalg.matmul",
  "category": "Matrix and vector products",
  "description": "Matrix product of two arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.matmul.html",
  "doc": "Matrix product of two arrays. The behavior depends on the arguments:\n- If both arguments are 2-D they are multiplied like conventional matrices\n- If either argument is N-D, N > 2, it is treated as a stack of matrices\n- If the first argument is 1-D, it is promoted to a matrix by prepending a 1 to its dimensions\n- If the second argument is 1-D, it is promoted to a matrix by appending a 1 to its dimensions\n\nThis is the same as the @ operator.",
  "code": "\n\n@array_function_dispatch(_matmul_dispatcher)\ndef matmul(x1, x2, /):\n    \"\"\"\n    Computes the matrix product.\n\n    This function is Array API compatible, contrary to\n    :func:\`numpy.matmul\`.\n\n    Parameters\n    ----------\n    x1 : array_like\n        The first input array.\n    x2 : array_like\n        The second input array.\n\n    Returns\n    -------\n    out : ndarray\n        The matrix product of the inputs.\n        This is a scalar only when both \`\`x1\`\`, \`\`x2\`\` are 1-d vectors.\n\n    Raises\n    ------\n    ValueError\n        If the last dimension of \`\`x1\`\` is not the same size as\n        the second-to-last dimension of \`\`x2\`\`.\n\n        If a scalar value is passed in.\n\n    See Also\n    --------\n    numpy.matmul\n\n    Examples\n    --------\n    For 2-D arrays it is the matrix product:\n\n    >>> a = np.array([[1, 0],\n    ...               [0, 1]])\n    >>> b = np.array([[4, 1],\n    ...               [2, 2]])\n    >>> np.linalg.matmul(a, b)\n    array([[4, 1],\n           [2, 2]])\n\n    For 2-D mixed with 1-D, the result is the usual.\n\n    >>> a = np.array([[1, 0],\n    ...               [0, 1]])\n    >>> b = np.array([1, 2])\n    >>> np.linalg.matmul(a, b)\n    array([1, 2])\n    >>> np.linalg.matmul(b, a)\n    array([1, 2])\n\n\n    Broadcasting is conventional for stacks of arrays\n\n    >>> a = np.arange(2 * 2 * 4).reshape((2, 2, 4))\n    >>> b = np.arange(2 * 2 * 4).reshape((2, 4, 2))\n    >>> np.linalg.matmul(a,b).shape\n    (2, 2, 2)\n    >>> np.linalg.matmul(a, b)[0, 1, 1]\n    98\n    >>> sum(a[0, 1, :] * b[0 , :, 1])\n    98\n\n    Vector, vector returns the scalar inner product, but neither argument\n    is complex-conjugated:\n\n    >>> np.linalg.matmul([2j, 3j], [2j, 3j])\n    (-13+0j)\n\n    Scalar multiplication raises an error.\n\n    >>> np.linalg.matmul([1,2], 3)\n    Traceback (most recent call last):\n    ...\n    ValueError: matmul: Input operand 1 does not have enough dimensions ...\n\n    \"\"\"\n    return _core_matmul(x1, x2)"
}
-/

open Std.Do

/-- Matrix multiplication for 2D matrices. 
    Computes the matrix product of two 2D arrays following standard matrix multiplication rules.
    The result matrix C has dimensions (m x p) where A is (m x n) and B is (n x p). -/
def matmul {m n p : Nat} (A : Vector (Vector Float n) m) (B : Vector (Vector Float p) n) : 
    Id (Vector (Vector Float p) m) :=
  sorry

/-- Specification: Matrix multiplication produces a result where each element is the dot product 
    of the corresponding row from the first matrix and column from the second matrix.
    
    Mathematical properties:
    1. Dimensions are compatible: A is m×n, B is n×p, result is m×p
    2. Each element C[i][j] = sum of A[i][k] * B[k][j] for k from 0 to n-1
    3. The operation preserves the fundamental matrix multiplication identity
    4. Non-commutativity: A*B ≠ B*A in general (handled by type system)
    5. Associativity: (A*B)*C = A*(B*C) when dimensions are compatible -/
theorem matmul_spec {m n p : Nat} (A : Vector (Vector Float n) m) (B : Vector (Vector Float p) n) :
    ⦃⌜True⌝⦄
    matmul A B
    ⦃⇓C => ⌜∀ i : Fin m, ∀ j : Fin p, 
              (C.get i).get j = List.sum (List.zipWith (· * ·) 
                (A.get i).toList 
                (List.map (fun row => row.get j) B.toList))⌝⦄ := by
  sorry