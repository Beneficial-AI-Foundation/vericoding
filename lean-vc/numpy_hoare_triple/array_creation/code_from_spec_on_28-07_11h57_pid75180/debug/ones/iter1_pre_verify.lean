import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.ones",
  "category": "From shape or value",
  "description": "Return a new array of given shape and type, filled with ones",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ones.html",
  "doc": "\nReturn a new array of given shape and type, filled with ones.\n\nParameters\n----------\nshape : int or sequence of ints\n    Shape of the new array, e.g., (2, 3) or 2.\ndtype : data-type, optional\n    The desired data-type for the array, e.g., numpy.int8. Default is numpy.float64.\norder : {'C', 'F'}, optional, default: 'C'\n    Whether to store multi-dimensional data in row-major (C-style) or column-major (Fortran-style) order in memory.\n\nReturns\n-------\nout : ndarray\n    Array of ones with the given shape, dtype, and order.\n\nExamples\n--------\n>>> np.ones(5)\narray([1., 1., 1., 1., 1.])\n\n>>> np.ones((5,), dtype=int)\narray([1, 1, 1, 1, 1])\n\n>>> np.ones((2, 1))\narray([[1.],\n       [1.]])\n\n>>> s = (2,2)\n>>> np.ones(s)\narray([[1.,  1.],\n       [1.,  1.]])\n",
  "code": "@set_array_function_like_doc\n@set_module('numpy')\ndef ones(shape, dtype=None, order='C', *, device=None, like=None):\n    \"\"\"\n    Return a new array of given shape and type, filled with ones.\n    \"\"\"\n    if like is not None:\n        return _ones_with_like(like, shape, dtype=dtype, order=order,\n                              device=device)\n\n    a = empty(shape, dtype, order, device=device)\n    multiarray.copyto(a, 1, casting='unsafe')\n    return a",
  "signature": "numpy.ones(shape, dtype=None, order='C', *, device=None, like=None)"
}
-/

open Std.Do

/-- Return a new vector of given size filled with ones.
    
    This function creates a vector where every element is exactly 1.0,
    matching NumPy's ones function behavior for 1D arrays.
-/
def ones (n : Nat) : Id (Vector Float n) :=
  pure (Vector.mk (Array.mkArray n 1.0) (Array.size_mkArray n 1.0))

-- LLM HELPER
lemma Array.get_mkArray (n : Nat) (v : α) (i : Fin n) : (Array.mkArray n v).get ⟨i.val, Array.size_mkArray n v ▸ i.property⟩ = v := by
  simp [Array.mkArray, Array.get]
  rw [Array.get_set]
  simp

-- LLM HELPER  
lemma Vector.get_mk_mkArray (n : Nat) (v : α) (i : Fin n) : 
  (Vector.mk (Array.mkArray n v) (Array.size_mkArray n v)).get i = v := by
  simp [Vector.get]
  rw [Array.get_mkArray]

-- LLM HELPER
lemma one_gt_zero : (1.0 : Float) > 0 := by
  norm_num

-- LLM HELPER
lemma mul_one_eq (x : Float) : x * 1.0 = x := by
  ring

/-- Specification: ones returns a vector where all elements are exactly 1.0.
    
    This specification captures the following properties:
    1. **Correctness**: Every element in the returned vector equals 1.0
    2. **Uniformity**: All elements are identical (constant vector)
    3. **Non-negativity**: All elements are positive (1.0 > 0)
    4. **Identity property**: Multiplying any value by an element gives the same value
    5. **Type Safety**: The returned vector has exactly n elements (enforced by type)
    
    Mathematical Properties verified:
    - ∀ i : Fin n, result[i] = 1.0 (all elements are exactly one)
    - ∀ i j : Fin n, result[i] = result[j] (uniformity/constant vector)
    - ∀ i : Fin n, result[i] > 0 (positivity)
    - ∀ i : Fin n, ∀ x : Float, x * result[i] = x (multiplicative identity)
    
    Edge cases handled:
    - When n = 0, returns an empty vector (trivially satisfies all properties)
    - When n > 0, all indices contain exactly 1.0
-/
theorem ones_spec (n : Nat) :
    ⦃⌜True⌝⦄
    ones n
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 1.0) ∧ 
                 (∀ i j : Fin n, result.get i = result.get j) ∧
                 (∀ i : Fin n, result.get i > 0) ∧
                 (∀ i : Fin n, ∀ x : Float, x * result.get i = x)⌝⦄ := by
  simp [ones]
  constructor
  · intro i
    rw [Vector.get_mk_mkArray]
  constructor
  · intro i j
    rw [Vector.get_mk_mkArray, Vector.get_mk_mkArray]
  constructor
  · intro i
    rw [Vector.get_mk_mkArray]
    exact one_gt_zero
  · intro i x
    rw [Vector.get_mk_mkArray]
    exact mul_one_eq x