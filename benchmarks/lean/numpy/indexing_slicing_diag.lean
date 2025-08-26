/-!
{
  "name": "numpy.diag",
  "category": "Diagonal operations",
  "description": "Extract a diagonal or construct a diagonal array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diag.html",
  "doc": "Extract a diagonal or construct a diagonal array.\n\nParameters\n----------\nv : array_like\n    If \`v\` is a 2-D array, return a copy of its \`k\`-th diagonal.\n    If \`v\` is a 1-D array, return a 2-D array with \`v\` on the \`k\`-th diagonal.\nk : int, optional\n    Diagonal in question. The default is 0. Use \`k>0\` for diagonals above the main diagonal, and \`k<0\` for diagonals below the main diagonal.\n\nReturns\n-------\nout : ndarray\n    The extracted diagonal or constructed diagonal array.",
  "code": "@array_function_dispatch(_diag_dispatcher)\ndef diag(v, k=0):\n    \"\"\"\n    Extract a diagonal or construct a diagonal array.\n\n    Parameters\n    ----------\n    v : array_like\n        If \`v\` is a 2-D array, return a copy of its \`k\`-th diagonal.\n        If \`v\` is a 1-D array, return a 2-D array with \`v\` on the \`k\`-th\n        diagonal.\n    k : int, optional\n        Diagonal in question. The default is 0. Use \`k>0\` for diagonals\n        above the main diagonal, and \`k<0\` for diagonals below the main\n        diagonal.\n\n    Returns\n    -------\n    out : ndarray\n        The extracted diagonal or constructed diagonal array.\n    \"\"\"\n    v = asanyarray(v)\n    s = v.shape\n    if len(s) == 1:\n        n = s[0] + abs(k)\n        res = zeros((n, n), v.dtype)\n        if k >= 0:\n            i = k\n        else:\n            i = (-k) * n\n        res[:n - k].flat[i::n + 1] = v\n        return res\n    elif len(s) == 2:\n        return diagonal(v, k)\n    else:\n        raise ValueError(\"Input must be 1- or 2-d.\")"
}
-/

/-- numpy.diag: Extract a diagonal or construct a diagonal array.
    
    For simplicity, this specification focuses on extracting the diagonal
    from a square matrix represented as a flattened vector.
    Given a flattened n×n matrix, returns the diagonal elements.
    
    This specification captures the essential mathematical property of
    diagonal extraction in a type-safe manner using Vector types.
-/
def diag {n : Nat} (matrix : Vector Float (n * n)) : Vector Float n :=
  sorry

/-- Specification: diag extracts diagonal elements from a flattened matrix.
    
    Mathematical Properties:
    1. Diagonal Extraction: For a flattened n×n matrix stored in row-major order,
       the diagonal elements are located at positions i*n + i for i ∈ [0, n).
    
    2. Type Safety: The function maintains type safety by using Vector types
       that encode the size information at the type level.
    
    3. Correctness: Each element in the result vector corresponds to a diagonal
       element from the original matrix, preserving the mathematical structure.
    
    This specification provides a foundation for formal verification of diagonal
    operations in numerical computing.
-/
theorem diag_spec {n : Nat} (matrix : Vector Float (n * n)) : 
    ∀ i : Fin n, (diag matrix).get i = matrix.get ⟨i.val * n + i.val, by sorry⟩ := by
  sorry