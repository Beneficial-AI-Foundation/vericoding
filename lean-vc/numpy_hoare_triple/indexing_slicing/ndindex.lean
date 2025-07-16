import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.ndindex",
  "category": "Index generation",
  "description": "An N-dimensional iterator object to index arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ndindex.html",
  "doc": "An N-dimensional iterator object to index arrays.\n\nGiven the shape of an array, an \`ndindex\` instance iterates over the N-dimensional index of the array.",
  "code": "@set_module('numpy')\nclass ndindex:\n    \"\"\"\n    An N-dimensional iterator object to index arrays.\n\n    Given the shape of an array, an \`ndindex\` instance iterates over\n    the N-dimensional index of the array.\n    \"\"\"\n\n    def __init__(self, *shape):\n        if len(shape) == 1 and isinstance(shape[0], tuple):\n            shape = shape[0]\n        x = as_strided(_nx.zeros(1), shape=shape,\n                       strides=_nx.zeros_like(shape))\n        self._it = _nx.nditer(x, flags=['multi_index', 'zerosize_ok'],\n                              order='C')\n\n    def __iter__(self):\n        return self\n\n    def __next__(self):\n        next(self._it)\n        return self._it.multi_index"
}
-/

/-- Generate N-dimensional indices for an array with given shape.
    Returns a vector of index tuples, where each tuple represents a valid
    N-dimensional index for an array with the specified dimensions.
    
    For a 2D array with shape (m, n), this generates all index pairs
    (i, j) where 0 ≤ i < m and 0 ≤ j < n, in C-order (row-major).
    
    Example: For shape (2, 3), generates [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)]
-/
def ndindex {m n : Nat} (shape : Nat × Nat) : Id (Vector (Fin m × Fin n) (m * n)) :=
  sorry

/-- Specification: ndindex generates all valid N-dimensional indices for a given shape.
    This comprehensive specification captures:
    1. The output contains exactly m*n index pairs for a 2D array of shape (m, n)
    2. Each index pair (i, j) satisfies the bounds: 0 ≤ i < m and 0 ≤ j < n
    3. The indices are generated in C-order (row-major): last dimension changes fastest
    4. All possible valid indices are included exactly once
    5. The ordering follows the pattern: (0,0), (0,1), ..., (0,n-1), (1,0), (1,1), ..., (m-1,n-1)
    
    Precondition: The shape parameters match the type parameters m and n
    Postcondition: The result contains all valid indices in the correct C-order
-/
theorem ndindex_spec {m n : Nat} (shape : Nat × Nat) (h_shape : shape = (m, n)) :
    ⦃⌜shape = (m, n)⌝⦄
    ndindex shape
    ⦃⇓indices => ⌜indices.size = m * n ∧
                   (∀ k : Fin (m * n), 
                      let (i, j) := indices.get k
                      i.val < m ∧ j.val < n) ∧
                   (∀ i : Fin m, ∀ j : Fin n,
                      ∃ k : Fin (m * n), indices.get k = (i, j)) ∧
                   (∀ k : Fin (m * n), 
                      let (i, j) := indices.get k
                      k.val = i.val * n + j.val)⌝⦄ := by
  sorry