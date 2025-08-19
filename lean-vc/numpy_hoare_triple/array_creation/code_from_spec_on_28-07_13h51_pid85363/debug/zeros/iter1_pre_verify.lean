import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.zeros",
  "category": "From shape or value",
  "description": "Return a new array of given shape and type, filled with zeros",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.zeros.html",
  "doc": "\nReturn a new array of given shape and type, filled with zeros.\n\nParameters\n----------\nshape : int or tuple of ints\n    Shape of the new array, e.g., (2, 3) or 2.\ndtype : data-type, optional\n    The desired data-type for the array, e.g., numpy.int8. Default is numpy.float64.\norder : {'C', 'F'}, optional, default: 'C'\n    Whether to store multi-dimensional data in row-major (C-style) or column-major (Fortran-style) order in memory.\n\nReturns\n-------\nout : ndarray\n    Array of zeros with the given shape, dtype, and order.\n\nExamples\n--------\n>>> np.zeros(5)\narray([ 0.,  0.,  0.,  0.,  0.])\n\n>>> np.zeros((5,), dtype=int)\narray([0, 0, 0, 0, 0])\n\n>>> np.zeros((2, 1))\narray([[ 0.],\n       [ 0.]])\n",
  "code": "@set_array_function_like_doc\n@set_module('numpy')\ndef zeros(shape, dtype=float, order='C', *, device=None, like=None):\n    \"\"\"\n    Return a new array of given shape and type, filled with zeros.\n    \"\"\"\n    if like is not None:\n        return _zeros_with_like(like, shape, dtype=dtype, order=order,\n                               device=device)\n\n    a = empty(shape, dtype, order, device=device)\n    multiarray.copyto(a, 0, casting='unsafe')\n    return a",
  "signature": "numpy.zeros(shape, dtype=float, order='C', *, device=None, like=None)"
}
-/

open Std.Do

/-- Return a new vector of given size, filled with zeros -/
def zeros (n : Nat) (α : Type) [Zero α] : Id (Vector α n) :=
  Vector.replicate n 0

-- LLM HELPER
lemma zero_add_eq {α : Type} [Add α] [Zero α] [AddMonoid α] (a : α) : 0 + a = a := 
  AddMonoid.zero_add a

-- LLM HELPER  
lemma add_zero_eq {α : Type} [Add α] [Zero α] [AddMonoid α] (a : α) : a + 0 = a := 
  AddMonoid.add_zero a

-- LLM HELPER
lemma mul_zero_eq {α : Type} [Mul α] [Zero α] [MulZeroClass α] (a : α) : a * 0 = 0 :=
  MulZeroClass.mul_zero a

-- LLM HELPER
lemma zero_mul_eq {α : Type} [Mul α] [Zero α] [MulZeroClass α] (a : α) : 0 * a = 0 :=
  MulZeroClass.zero_mul a

-- LLM HELPER
lemma vector_replicate_get (n : Nat) (α : Type) (a : α) (i : Fin n) : 
  (Vector.replicate n a).get i = a := by
  simp [Vector.replicate, Vector.get]

/-- Specification: zeros returns a vector where all elements are zero
    This comprehensive specification captures:
    1. All elements equal to zero (basic property)
    2. The result is the additive identity for vector addition
    3. The sum of all elements is zero (for numeric types)
    4. Scalar multiplication by any value preserves the zero property
    5. The dot product with any vector is zero
    6. The norm/magnitude is zero (for types with norm)
    7. Element-wise operations preserve zero structure
-/
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
                 (n > 0 → result.get ⟨0, Nat.zero_lt_of_zero_lt_one (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by assumption)))⟩ = 0)⌝⦄ := by
  simp [zeros]
  constructor
  · intro i
    exact vector_replicate_get n α 0 i
  constructor
  · intro v i
    constructor
    · by_cases h : AddMonoid α
      · exact zero_add_eq (v.get i)
      · simp [Vector.replicate, Vector.get]
    · by_cases h : AddMonoid α  
      · exact add_zero_eq (v.get i)
      · simp [Vector.replicate, Vector.get]
  constructor
  · intro scalar i
    by_cases h : MulZeroClass α
    · simp [Vector.replicate, Vector.get]
      exact mul_zero_eq scalar
    · simp [Vector.replicate, Vector.get]
  constructor
  · intro v i
    by_cases h : MulZeroClass α
    · simp [Vector.replicate, Vector.get]
      exact zero_mul_eq (v.get i)
    · simp [Vector.replicate, Vector.get]
  · intro h_pos
    simp [Vector.replicate, Vector.get]