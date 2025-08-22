import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.dstack",
  "category": "Joining Arrays",
  "description": "Stack arrays in sequence depth wise (along third axis)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.dstack.html",
  "doc": "Stack arrays in sequence depth wise (along third axis).\n\nThis is equivalent to concatenation along the third axis after 2-D arrays\nof shape \`(M,N)\` have been reshaped to \`(M,N,1)\` and 1-D arrays of shape\n\`(N,)\` have been reshaped to \`(1,N,1)\`. Rebuilds arrays divided by\n\`dsplit\`.\n\nThis function makes most sense for arrays with up to 3 dimensions. For\ninstance, for pixel-data with a height (first axis), width (second axis),\nand r/g/b channels (third axis). The functions \`concatenate\`, \`stack\` and\n\`block\` provide more general stacking and concatenation operations.\n\nParameters\n----------\ntup : sequence of arrays\n    The arrays must have the same shape along all but the third axis.\n    1-D or 2-D arrays must have the same shape.\n\nReturns\n-------\nstacked : ndarray\n    The array formed by stacking the given arrays, will be at least 3-D.\n\nExamples\n--------\n>>> a = np.array((1,2,3))\n>>> b = np.array((2,3,4))\n>>> np.dstack((a,b))\narray([[[1, 2],\n        [2, 3],\n        [3, 4]]])\n>>> a = np.array([[1],[2],[3]])\n>>> b = np.array([[2],[3],[4]])\n>>> np.dstack((a,b))\narray([[[1, 2]],\n       [[2, 3]],\n       [[3, 4]]])",
  "code": "# Implementation in numpy/lib/_shape_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.dstack(tup)"
}
-/

open Std.Do

/-- numpy.dstack: Stack arrays in sequence depth wise (along third axis).

    For a sequence of 1D arrays (vectors), this function stacks them along a new third axis,
    creating a 3D array. Each input vector becomes a "slice" in the depth dimension.
    
    For 1D inputs of length n, the output shape is (1, n, k) where k is the number of arrays.
    This is because 1D arrays are first reshaped to (1, n) then stacked along axis 2.
    
    The result is always at least 3-dimensional.
-/
def numpy_dstack {k n : Nat} (arrays : Vector (Vector Float n) (k + 1)) : 
    Id (Vector (Vector (Vector Float (k + 1)) n) 1) :=
  sorry

/-- Specification: numpy.dstack stacks 1D arrays along the third axis.
    
    For k+1 input vectors each of length n:
    - The output has shape (1, n, k+1)
    - Element at position [0][i][j] equals arrays[j][i]
    
    This specification captures the core behavior where each input vector
    contributes one "layer" in the depth dimension of the output.
-/
theorem numpy_dstack_spec {k n : Nat} (arrays : Vector (Vector Float n) (k + 1)) :
    ⦃⌜True⌝⦄
    numpy_dstack arrays
    ⦃⇓result => ⌜
      -- The outer dimension has size 1
      result.toList.length = 1 ∧
      -- For the single element at index 0, it has n rows
      (result.get ⟨0, by simp⟩).toList.length = n ∧
      -- Each row has k+1 elements (depth dimension)
      (∀ i : Fin n, ((result.get ⟨0, by simp⟩).get i).toList.length = k + 1) ∧
      -- Elements are correctly positioned: result[0][i][j] = arrays[j][i]
      (∀ i : Fin n, ∀ j : Fin (k + 1), 
        ((result.get ⟨0, by simp⟩).get i).get j = (arrays.get j).get i)
    ⌝⦄ := by
  sorry