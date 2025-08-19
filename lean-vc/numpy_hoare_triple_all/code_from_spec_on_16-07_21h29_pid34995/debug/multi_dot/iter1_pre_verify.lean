import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.linalg.multi_dot",
  "category": "Matrix and vector products",
  "description": "Compute the dot product of two or more arrays in a single function call",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.multi_dot.html",
  "doc": "Compute the dot product of two or more arrays in a single function call, while automatically selecting the fastest evaluation order.\n\nmulti_dot chains numpy.dot and uses optimal parenthesization of the matrices. Depending on the shapes of the matrices, this can speed up the multiplication a lot.\n\nIf the first argument is 1-D it is treated as a row vector. If the last argument is 1-D it is treated as a column vector. The other arguments must be 2-D.\n\nThink of multi_dot as: def multi_dot(arrays): return functools.reduce(np.dot, arrays)",
  "code": "\n\n@array_function_dispatch(_multidot_dispatcher)\ndef multi_dot(arrays, *, out=None):\n    \"\"\"\n    Compute the dot product of two or more arrays in a single function call,\n    while automatically selecting the fastest evaluation order.\n\n    \`multi_dot\` chains \`numpy.dot\` and uses optimal parenthesization\n    of the matrices [1]_ [2]_. Depending on the shapes of the matrices,\n    this can speed up the multiplication a lot.\n\n    If the first argument is 1-D it is treated as a row vector.\n    If the last argument is 1-D it is treated as a column vector.\n    The other arguments must be 2-D.\n\n    Think of \`multi_dot\` as::\n\n        def multi_dot(arrays): return functools.reduce(np.dot, arrays)\n\n\n    Parameters\n    ----------\n    arrays : sequence of array_like\n        If the first argument is 1-D it is treated as row vector.\n        If the last argument is 1-D it is treated as column vector.\n        The other arguments must be 2-D.\n    out : ndarray, optional\n        Output argument. This must have the exact kind that would be returned\n        if it was not used. In particular, it must have the right type, must be\n        C-contiguous, and its dtype must be the dtype that would be returned\n        for \`dot(a, b)\`. This is a performance feature. Therefore, if these\n        conditions are not met, an exception is raised, instead of attempting\n        to be flexible.\n\n    Returns\n    -------\n    output : ndarray\n        Returns the dot product of the supplied arrays.\n\n    See Also\n    --------\n    numpy.dot : dot multiplication with two arguments.\n\n    References\n    ----------\n\n    .. [1] Cormen, \"Introduction to Algorithms\", Chapter 15.2, p. 370-378\n    .. [2] https://en.wikipedia.org/wiki/Matrix_chain_multiplication\n\n    Examples\n    --------\n    \`multi_dot\` allows you to write::\n\n    >>> import numpy as np\n    >>> from numpy.linalg import multi_dot\n    >>> # Prepare some data\n    >>> A = np.random.random((10000, 100))\n    >>> B = np.random.random((100, 1000))\n    >>> C = np.random.random((1000, 5))\n    >>> D = np.random.random((5, 333))\n    >>> # the actual dot multiplication\n    >>> _ = multi_dot([A, B, C, D])\n\n    instead of::\n\n    >>> _ = np.dot(np.dot(np.dot(A, B), C), D)\n    >>> # or\n    >>> _ = A.dot(B).dot(C).dot(D)\n\n    Notes\n    -----\n    The cost for a matrix multiplication can be calculated with the\n    following function::\n\n        def cost(A, B):\n            return A.shape[0] * A.shape[1] * B.shape[1]\n\n    Assume we have three matrices\n    :math:\`A_{10 \\times 100}, B_{100 \\times 5}, C_{5 \\times 50}\`.\n\n    The costs for the two different parenthesizations are as follows::\n\n        cost((AB)C) = 10*100*5 + 10*5*50   = 5000 + 2500   = 7500\n        cost(A(BC)) = 10*100*50 + 100*5*50 = 50000 + 25000 = 75000\n\n    \"\"\"\n    n = len(arrays)\n    # optimization only makes sense for len(arrays) > 2\n    if n < 2:\n        raise ValueError(\"Expecting at least two arrays.\")\n    elif n == 2:\n        return dot(arrays[0], arrays[1], out=out)\n\n    arrays = [asanyarray(a) for a in arrays]\n\n    # save original ndim to reshape the result array into the proper form later\n    ndim_first, ndim_last = arrays[0].ndim, arrays[-1].ndim\n    # Explicitly convert vectors to 2D arrays to keep the logic of the internal\n    # _multi_dot_* functions as simple as possible.\n    if arrays[0].ndim == 1:\n        arrays[0] = atleast_2d(arrays[0])\n    if arrays[-1].ndim == 1:\n        arrays[-1] = atleast_2d(arrays[-1]).T\n    _assert_2d(*arrays)\n\n    # _multi_dot_three is much faster than _multi_dot_matrix_chain_order\n    if n == 3:\n        result = _multi_dot_three(arrays[0], arrays[1], arrays[2], out=out)\n    else:\n        order = _multi_dot_matrix_chain_order(arrays)\n        result = _multi_dot(arrays, order, 0, n - 1, out=out)\n\n    # return proper shape\n    if ndim_first == 1 and ndim_last == 1:\n        return result[0, 0]  # scalar\n    elif ndim_first == 1 or ndim_last == 1:\n        return result.ravel()  # 1-D\n    else:\n        return result"
}
-/

-- LLM HELPER
def matmul {n₁ n₂ n₃ : Nat} 
    (A : Vector (Vector Float n₂) n₁) 
    (B : Vector (Vector Float n₃) n₂) : 
    Vector (Vector Float n₃) n₁ :=
  Vector.tabulate n₁ (fun i => 
    Vector.tabulate n₃ (fun j =>
      List.sum (List.zipWith (· * ·) 
        (A.get i).toList 
        (List.map (fun row => row.get j) B.toList))))

-- LLM HELPER
def cost_ab_c (n₁ n₂ n₃ n₄ : Nat) : Nat :=
  n₁ * n₂ * n₃ + n₁ * n₃ * n₄

-- LLM HELPER
def cost_a_bc (n₁ n₂ n₃ n₄ : Nat) : Nat :=
  n₂ * n₃ * n₄ + n₁ * n₂ * n₄

/-- Multi-dot product: compute the dot product of multiple matrices in a single function call
    with optimal parenthesization. This function performs a chain of matrix multiplications
    A₁ × A₂ × ... × Aₙ where the parenthesization is chosen to minimize computational cost.
    
    For three matrices A, B, C, this computes A × B × C with the optimal evaluation order.
    The result is independent of parenthesization due to associativity of matrix multiplication. -/
def multi_dot {n₁ n₂ n₃ n₄ : Nat} 
    (A : Vector (Vector Float n₂) n₁) 
    (B : Vector (Vector Float n₃) n₂) 
    (C : Vector (Vector Float n₄) n₃) : 
    Id (Vector (Vector Float n₄) n₁) :=
  if cost_ab_c n₁ n₂ n₃ n₄ ≤ cost_a_bc n₁ n₂ n₃ n₄ then
    Id.pure (matmul (matmul A B) C)
  else
    Id.pure (matmul A (matmul B C))

/-- Specification: Multi-dot performs a chain of matrix multiplications with optimal parenthesization.
    
    Mathematical properties:
    1. Associativity: (A × B) × C = A × (B × C) - the result is independent of parenthesization
    2. Dimension compatibility: A is n₁×n₂, B is n₂×n₃, C is n₃×n₄, result is n₁×n₄
    3. Element-wise computation: result[i][j] equals the triple sum over intermediate indices
    4. Optimal evaluation order: the implementation chooses the parenthesization that minimizes 
       the total number of scalar multiplications needed
    5. Correctness: the result equals the sequential application of matrix multiplications
    6. Non-empty constraint: at least two matrices are required (enforced by signature)
    
    This specification captures the essential mathematical behavior while abstracting away 
    the optimization details. The key insight is that matrix multiplication is associative,
    so different parenthesizations yield the same mathematical result. -/
theorem multi_dot_spec {n₁ n₂ n₃ n₄ : Nat} 
    (A : Vector (Vector Float n₂) n₁) 
    (B : Vector (Vector Float n₃) n₂) 
    (C : Vector (Vector Float n₄) n₃) :
    ⦃⌜True⌝⦄
    multi_dot A B C
    ⦃⇓result => ⌜result.toList.length = n₁ ∧ 
                  ∀ i : Fin n₁, (result.get i).toList.length = n₄ ∧
                  ∀ i : Fin n₁, ∀ j : Fin n₄, 
                    ∃ matrix_product : Float,
                    (result.get i).get j = matrix_product ∧ 
                    matrix_product = List.sum (List.zipWith (· * ·) 
                      (A.get i).toList 
                      (List.map (fun row => 
                        List.sum (List.zipWith (· * ·) 
                          row.toList 
                          (List.map (fun col => col.get j) C.toList))) 
                        B.toList))⌝⦄ := by
  rw [hwpSpec_def]
  simp [multi_dot]
  intro h
  split <;> simp [Id.pure]
  · constructor
    · simp [matmul, Vector.toList_tabulate]
    · constructor
      · intro i
        simp [matmul, Vector.toList_tabulate]
      · intro i j
        simp [matmul]
        use List.sum (List.zipWith (· * ·) 
          (A.get i).toList 
          (List.map (fun row => 
            List.sum (List.zipWith (· * ·) 
              row.toList 
              (List.map (fun col => col.get j) C.toList))) 
            B.toList))
        constructor
        · rfl
        · rfl
  · constructor
    · simp [matmul, Vector.toList_tabulate]
    · constructor
      · intro i
        simp [matmul, Vector.toList_tabulate]
      · intro i j
        simp [matmul]
        use List.sum (List.zipWith (· * ·) 
          (A.get i).toList 
          (List.map (fun row => 
            List.sum (List.zipWith (· * ·) 
              row.toList 
              (List.map (fun col => col.get j) C.toList))) 
            B.toList))
        constructor
        · rfl
        · rfl