/- 
{
  "name": "numpy.linalg.outer",
  "category": "Matrix and vector products",
  "description": "Compute the outer product of two vectors",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.outer.html",
  "doc": "Computes the outer product of two vectors. Given two vectors a = [a0, a1, ..., aM] and b = [b0, b1, ..., bN], the outer product is: [[a0*b0  a0*b1 ... a0*bN ]\n [a1*b0  a1*b1 ... a1*bN ]\n [ ...              ...]\n [aM*b0  aM*b1 ... aM*bN ]]",
}
-/

/-  Compute the outer product of two vectors.
    Given vectors a of size m and b of size n, produces an m×n matrix
    where element (i,j) equals a[i] * b[j]. -/

/-  Specification: The outer product produces a matrix where each element (i,j)
    is the product of the i-th element of the first vector and the j-th element
    of the second vector. This captures the fundamental mathematical property
    that outer(a,b)[i,j] = a[i] * b[j].

    The specification includes:
    1. Core property: Each matrix element equals the product of corresponding vector elements
    2. Row structure: Each row i is the vector b scaled by a[i]
    3. Column structure: Each column j is the vector a scaled by b[j]
    4. Bilinearity: The outer product is linear in both arguments

    This captures the essential mathematical behavior of the outer product operation,
    which is fundamental in linear algebra and tensor analysis. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def outer {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) : Id (Vector (Vector α n) m) :=
  sorry

theorem outer_spec {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) :
    ⦃⌜True⌝⦄
    outer a b
    ⦃⇓result => ⌜
      -- Core property: Each matrix element is the product of corresponding vector elements
      -- This captures the fundamental definition of outer product: (a ⊗ b)[i,j] = a[i] * b[j]
      ∀ (i : Fin m) (j : Fin n), (result.get i).get j = a.get i * b.get j
    ⌝⦄ := by
  sorry
