import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.resize",
  "category": "Adding Removing Elements",
  "description": "Return a new array with the specified shape",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.resize.html",
  "doc": "Return a new array with the specified shape.\n\nIf the new array is larger than the original array, then the new\narray is filled with repeated copies of \`a\`. Note that this behavior\nis different from a.resize(new_shape) which fills with zeros instead\nof repeated copies of \`a\`.\n\nParameters\n----------\na : array_like\n    Array to be resized.\nnew_shape : int or tuple of ints\n    Shape of resized array.\n\nReturns\n-------\nreshaped_array : ndarray\n    The new array is formed from the data in the old array, repeated\n    if necessary to fill out the required number of elements. The\n    data are repeated iterating over the array in C-order.\n\nExamples\n--------\n>>> a=np.array([[0,1],[2,3]])\n>>> np.resize(a,(2,3))\narray([[0, 1, 2],\n       [3, 0, 1]])\n>>> np.resize(a,(1,4))\narray([[0, 1, 2, 3]])\n>>> np.resize(a,(2,4))\narray([[0, 1, 2, 3],\n       [0, 1, 2, 3]])",
  "code": "@array_function_dispatch(_size_dispatcher)\ndef size(a, axis=None):\n    \"\"\"\n    Return the number of elements along a given axis.\n    \"\"\"\n    if axis is None:\n        try:\n            return a.size\n        except AttributeError:\n            return asarray(a).size\n    else:\n        try:\n            return a.shape[axis]\n        except AttributeError:\n            return asarray(a).shape[axis]",
  "source_location": "C implementation in numpy/_core/src/multiarray/multiarraymodule.c",
  "signature": "numpy.resize(a, new_shape)"
}
-/

open Std.Do

/-- Return a new vector with the specified size by repeating elements from the input vector.
    If the new size is larger, elements are repeated cyclically.
    If the new size is smaller, only the first elements are taken. -/
def resize {n : Nat} {α : Type} (a : Vector α n) (new_size : Nat) : Id (Vector α new_size) :=
  sorry

/-- Specification: resize creates a new vector of the specified size by either:
    1. Taking the first `new_size` elements if `new_size ≤ n`
    2. Repeating the original elements cyclically if `new_size > n` and `n > 0`
    
    The function handles three cases:
    - Shrinking: new_size < n → takes first new_size elements
    - Same size: new_size = n → returns identical vector
    - Growing: new_size > n → repeats elements cyclically (when n > 0) -/
theorem resize_spec {n : Nat} {α : Type} (a : Vector α n) (new_size : Nat) :
    ⦃⌜True⌝⦄
    resize a new_size
    ⦃⇓result => ⌜(∀ i : Fin new_size, 
        if h : i.val < n then
          result.get i = a.get ⟨i.val, h⟩
        else if hn : n > 0 then
          result.get i = a.get ⟨i.val % n, Nat.mod_lt i.val hn⟩
        else
          True)⌝⦄ := by
  sorry