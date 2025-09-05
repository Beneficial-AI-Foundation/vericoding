/- 
{
  "name": "ufunc.outer",
  "category": "Outer Product Method",
  "description": "Apply ufunc to all pairs (a, b) with a in A and b in B",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.outer.html",
  "signature": "ufunc.outer(A, B, /, **kwargs)",
  "parameters": {
    "A": "First input array",
    "B": "Second input array",
    "**kwargs": "Additional keyword arguments passed to the ufunc"
  },
  "example": "np.multiply.outer([1, 2, 3], [4, 5, 6])\n# Returns:\n# array([[ 4,  5,  6],\n#        [ 8, 10, 12],\n#        [12, 15, 18]])",
  "notes": [
    "Result has dimension A.ndim + B.ndim",
    "More general than numpy.outer which only works on 1-D arrays"
  ]
}
-/

/-  
Universal function outer method: Apply a binary operator to all pairs (a, b) 
with a in A and b in B.

For two 1-D vectors A = [a₁, a₂, ..., aₘ] and B = [b₁, b₂, ..., bₙ], 
the outer product produces an m×n matrix where result[i,j] = op(A[i], B[j]).

This generalizes the concept of outer product beyond just multiplication:
- When op = (*), this becomes the traditional outer product
- When op = (+), this becomes the sum of all pairs
- When op = (^), this becomes the power of all pairs

The result has shape (m, n) where m is the length of A and n is the length of B.
-/

/-  
Specification: outer applies a binary operator to all pairs of elements
from two input vectors, producing a matrix result.

Precondition: True (works for any two vectors and binary operation)
Postcondition:
- Result has dimensions m × n (outer dimensions of input vectors)
- Each element result[i][j] equals op(a[i], b[j])
- The result preserves the structure of the Cartesian product of the inputs
- All pairs (i,j) with i ∈ [0..m-1] and j ∈ [0..n-1] are covered exactly once

Mathematical Properties:
- result[i][j] = op(a[i], b[j]) for all valid i, j
- The result matrix has the same number of rows as the first input vector
- The result matrix has the same number of columns as the second input vector
- For commutative operations: outer(op, a, b)[i][j] = outer(op, b, a)[j][i]
- For associative operations: outer preserves the algebraic structure
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def outer {m n : Nat} (op : Float → Float → Float) (a : Vector Float m) (b : Vector Float n) : 
    Id (Vector (Vector Float n) m) :=
  sorry

theorem outer_spec {m n : Nat} (op : Float → Float → Float) (a : Vector Float m) (b : Vector Float n) :
    ⦃⌜True⌝⦄
    outer op a b
    ⦃⇓result => ⌜
      -- Result has correct outer dimensions
      result.size = m ∧
      -- Each row has correct inner dimension
      (∀ i : Fin m, (result.get i).size = n) ∧
      -- Each element is the result of applying the operator to the corresponding pair
      (∀ i : Fin m, ∀ j : Fin n, (result.get i).get j = op (a.get i) (b.get j)) ∧
      -- Structural property: result represents all pairs from Cartesian product
      (∀ i : Fin m, ∀ j : Fin n, ∃ ai bj, ai = a.get i ∧ bj = b.get j ∧ (result.get i).get j = op ai bj)
    ⌝⦄ := by
  sorry
