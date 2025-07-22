import Std.Do.Triple
import Std.Tactic.Do
/-!
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
lemma vector_replicate_get (n : Nat) (α : Type) [Zero α] (i : Fin n) :
  (Vector.replicate n (0 : α)).get i = 0 := by
  simp [Vector.replicate, Vector.get]

-- LLM HELPER
lemma zero_add (α : Type) [Zero α] [Add α] (a : α) : 0 + a = a := by
  simp [Zero.zero]

-- LLM HELPER
lemma add_zero (α : Type) [Zero α] [Add α] (a : α) : a + 0 = a := by
  simp [Zero.zero]

-- LLM HELPER
lemma mul_zero (α : Type) [Zero α] [Mul α] (a : α) : a * 0 = 0 := by
  simp [Zero.zero]

-- LLM HELPER
lemma zero_mul (α : Type) [Zero α] [Mul α] (a : α) : 0 * a = 0 := by
  simp [Zero.zero]

-- LLM HELPER
lemma fin_pos_zero (n : Nat) (h : n > 0) : ⟨0, h⟩ = (0 : Fin n) := by
  rfl

/-- Specification: zeros returns a vector where all elements are zero -/
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
                   result.get i * v.get i = 0)⌝⦄ := by
  unfold zeros
  simp only [Id.pure_eq, Vector.replicate]
  constructor
  · trivial
  · intro result
    simp [Vector.get, Vector.replicate]
    constructor
    · intro i
      simp [Vector.get_mk, List.get_replicate]
    · constructor
      · intro v i
        simp [Vector.get_mk, List.get_replicate]
        constructor
        · simp [add_zero]
        · simp [zero_add]
      · constructor
        · intro scalar i
          simp [Vector.get_mk, List.get_replicate, mul_zero]
        · intro v i
          simp [Vector.get_mk, List.get_replicate, zero_mul]