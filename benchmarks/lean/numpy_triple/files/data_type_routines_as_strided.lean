/- 
{
  "name": "numpy.as_strided",
  "category": "Memory and Striding",
  "description": "Create a view into the array with the given shape and strides",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.lib.stride_tricks.as_strided.html",
  "doc": "Create a view into the array with the given shape and strides.\n\nWarning: This function has to be used with extreme care, see notes.\n\nParameters\n----------\nx : ndarray\n    Array to create a new view for.\nshape : sequence of int, optional\n    The shape of the new array. Defaults to x.shape.\nstrides : sequence of int, optional\n    The strides of the new array. Defaults to x.strides.\nsubok : bool, optional\n    If True, subclasses are preserved.\nwriteable : bool, optional\n    If set to False, the returned array will always be readonly.\n\nReturns\n-------\nview : ndarray\n\nNotes\n-----\nas_strided creates a view into the array given the exact strides and shape. This means it manipulates the internal data structure of ndarray and, if done incorrectly, the array elements can point to invalid memory and can corrupt results or crash your program.\n\nExamples\n--------\n>>> x = np.array([1, 2, 3, 4, 5])\n>>> np.lib.stride_tricks.as_strided(x, shape=(3,), strides=(8,))\narray([1, 2, 3])",
}
-/

/-  numpy.as_strided: Create a view into the array with the given shape and strides.

    Creates a new view of an array with specified shape and strides.
    This is a simplified version that focuses on the core mathematical
    property: creating a view with a different shape but accessing
    elements from the original array based on stride patterns.

    For safety, we restrict to cases where the new shape is smaller
    than or equal to the original array size.
-/

/-  Specification: numpy.as_strided creates a view with specified strides.

    Precondition: The strided access must be valid (m * stride ≤ n)
    Postcondition: Each element in the result is taken from the original
    array at positions determined by the stride pattern.

    For element i in the result, it equals x[i * stride].
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_as_strided {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) : Id (Vector Float m) :=
  sorry

theorem numpy_as_strided_spec {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) :
    ⦃⌜m * stride ≤ n ∧ stride > 0⌝⦄
    numpy_as_strided x stride h_valid h_stride_pos
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = x.get ⟨i.val * stride, 
                   by have h1 : i.val < m := i.isLt
                      have h2 : i.val * stride < m * stride := by
                        apply Nat.mul_lt_mul_of_pos_right h1 h_stride_pos
                      exact Nat.lt_of_lt_of_le h2 h_valid⟩⌝⦄ := by
  sorry
