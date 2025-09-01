/- 
{
  "name": "numpy.zeros",
  "category": "From shape or value",
  "description": "Return a new array of given shape and type, filled with zeros",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.zeros.html",
  "doc": "\nReturn a new array of given shape and type, filled with zeros.\n\nParameters\n----------\nshape : int or tuple of ints\n    Shape of the new array, e.g., (2, 3) or 2.\ndtype : data-type, optional\n    The desired data-type for the array, e.g., numpy.int8. Default is numpy.float64.\norder : {'C', 'F'}, optional, default: 'C'\n    Whether to store multi-dimensional data in row-major (C-style) or column-major (Fortran-style) order in memory.\n\nReturns\n-------\nout : ndarray\n    Array of zeros with the given shape, dtype, and order.\n\nExamples\n--------\n>>> np.zeros(5)\narray([ 0.,  0.,  0.,  0.,  0.])\n\n>>> np.zeros((5,), dtype=int)\narray([0, 0, 0, 0, 0])\n\n>>> np.zeros((2, 1))\narray([[ 0.],\n       [ 0.]])\n",
  "signature": "numpy.zeros(shape, dtype=float, order='C', *, device=None, like=None)"
}
-/

/-  Return a new vector of given size, filled with zeros -/

/-  Specification: zeros returns a vector where all elements are zero
    This comprehensive specification captures:
    1. All elements equal to zero (basic property)
    2. The result is the additive identity for vector addition
    3. The sum of all elements is zero (for numeric types)
    4. Scalar multiplication by any value preserves the zero property
    5. The dot product with any vector is zero
    6. The norm/magnitude is zero (for types with norm)
    7. Element-wise operations preserve zero structure
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def zeros (n : Nat) (α : Type) [Zero α] : Id (Vector α n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem zeros_spec (n : Nat) (α : Type) [Zero α] [Add α] [Mul α] :
    ⦃⌜True⌝⦄
    zeros n α
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 0) ∧
                 (∀ v : Vector α n, ∀ i : Fin n, 
                   (result.get i + v.get i = v.get i) ∧ 
                   (v.get i + result.get i = v.get i)) ∧
                 (∀ scalar : α, ∀ i : Fin n,
                   scalar * result.get i = 0) ∧
                 (∀ v : Vector α n, ∀ i : Fin n,
                   result.get i * v.get i = 0) ∧
                 (n > 0 → result.get ⟨0, sorry⟩ = 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
