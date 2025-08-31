/- 
{
  "name": "numpy.flip",
  "category": "Rearranging Elements",
  "description": "Reverse the order of elements in an array along the given axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.flip.html",
  "doc": "Reverse the order of elements in an array along the given axis.\n\nThe shape of the array is preserved, but the elements are reordered.\n\nParameters\n----------\nm : array_like\n    Input array.\naxis : None or int or tuple of ints, optional\n    Axis or axes along which to flip over. The default,\n    axis=None, will flip over all of the axes of the input array.\n    If axis is negative it counts from the last to the first axis.\n\n    If axis is a tuple of ints, flipping is performed on all of the axes\n    specified in the tuple.\n\nReturns\n-------\nout : array_like\n    A view of \`m\` with the entries of axis reversed. Since a view is\n    returned, this operation is done in constant time.\n\nExamples\n--------\n>>> A = np.arange(8).reshape((2,2,2))\n>>> A\narray([[[0, 1],\n        [2, 3]],\n       [[4, 5],\n        [6, 7]]])\n>>> np.flip(A, 0)\narray([[[4, 5],\n        [6, 7]],\n       [[0, 1],\n        [2, 3]]])\n>>> np.flip(A, 1)\narray([[[2, 3],\n        [0, 1]],\n       [[6, 7],\n        [4, 5]]])\n>>> np.flip(A)\narray([[[7, 6],\n        [5, 4]],\n       [[3, 2],\n        [1, 0]]])\n>>> np.flip(A, (0, 2))\narray([[[5, 4],\n        [7, 6]],\n       [[1, 0],\n        [3, 2]]])\n>>> A = np.random.randn(3,4,5)\n>>> np.all(np.flip(A,2) == A[:,:,::-1,...])\nTrue",
  "source_location": "numpy/lib/_function_base_impl.py",
  "signature": "numpy.flip(m, axis=None)"
}
-/

/-  Reverses the order of elements in a vector (1D case of numpy.flip).
    
    This function reverses the order of all elements in the input vector.
    For a vector [a, b, c, d], it returns [d, c, b, a].
    
    In the general n-dimensional case, numpy.flip can reverse along specific axes,
    but this specification focuses on the 1D case where all elements are reversed. -/

/-  Specification: numpy_flip reverses the order of elements in the vector.
    
    Mathematical properties:
    1. Element mapping: The element at position i in the result equals the element 
       at position (n-1-i) in the input
    2. Involution property: Applying numpy_flip twice returns the original vector
    3. Size preservation: The output has the same size as the input (enforced by types)
    
    Sanity checks:
    - For n=0 (empty vector), returns empty vector
    - For n=1 (single element), returns the same vector
    - For n>1, first element becomes last, last becomes first -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_flip {n : Nat} (m : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem numpy_flip_spec {n : Nat} (m : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_flip m
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = m.get ⟨n - 1 - i.val, by
      have h : i.val < n := i.isLt
      omega⟩⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
