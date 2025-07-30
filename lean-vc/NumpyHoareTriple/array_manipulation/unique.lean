import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.unique",
  "category": "Adding Removing Elements",
  "description": "Find the unique elements of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.unique.html",
  "doc": "Find the unique elements of an array.\n\nReturns the sorted unique elements of an array. There are three optional\noutputs in addition to the unique elements:\n\n* the indices of the input array that give the unique values\n* the indices of the unique array that reconstruct the input array\n* the number of times each unique value comes up in the input array\n\nParameters\n----------\nar : array_like\n    Input array. Unless \`axis\` is specified, this will be flattened if it\n    is not already 1-D.\nreturn_index : bool, optional\n    If True, also return the indices of \`ar\` (along the specified axis,\n    if provided, or in the flattened array) that result in the unique array.\nreturn_inverse : bool, optional\n    If True, also return the indices of the unique array (for the specified\n    axis, if provided) that can be used to reconstruct \`ar\`.\nreturn_counts : bool, optional\n    If True, also return the number of times each unique item appears\n    in \`ar\`.\naxis : int or None, optional\n    The axis to operate on. If None, \`ar\` will be flattened. If an integer,\n    the subarrays indexed by the given axis will be flattened and treated\n    as the elements of a 1-D array with the dimension of the given axis,\n    see the notes for more details. Object arrays or structured arrays\n    that contain objects are not supported if the \`axis\` kwarg is used. The\n    default is None.\nequal_nan : bool, optional\n    If True, collapses multiple NaN values in the return array into one.\n\n    .. versionadded:: 1.24\n\nReturns\n-------\nunique : ndarray\n    The sorted unique values.\nunique_indices : ndarray, optional\n    The indices of the first occurrences of the unique values in the\n    original array. Only provided if \`return_index\` is True.\nunique_inverse : ndarray, optional\n    The indices to reconstruct the original array from the\n    unique array. Only provided if \`return_inverse\` is True.\nunique_counts : ndarray, optional\n    The number of times each of the unique values comes up in the\n    original array. Only provided if \`return_counts\` is True.\n\nExamples\n--------\n>>> np.unique([1, 1, 2, 2, 3, 3])\narray([1, 2, 3])\n>>> a = np.array([[1, 1], [2, 3]])\n>>> np.unique(a)\narray([1, 2, 3])",
  "code": "# Implementation in numpy/lib/_arraysetops_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_arraysetops_impl.py",
  "signature": "numpy.unique(ar, return_index=False, return_inverse=False, return_counts=False, axis=None, *, equal_nan=True)"
}
-/

open Std.Do

/-- numpy.unique: Find the unique elements of a vector and return them sorted.
    
    Returns a new vector containing each distinct element from the input exactly once,
    sorted in ascending order. This is a simplified version that only returns the 
    unique values without the optional indices or counts.
    
    The output size depends on the number of unique elements in the input.
-/
def numpy_unique {n : Nat} (arr : Vector Float n) : Id (Σ m : Nat, Vector Float m) :=
  sorry

/-- Specification: numpy.unique returns a sorted vector containing each distinct element 
    from the input exactly once.
    
    Precondition: True
    Postcondition: 
    - The result is sorted in ascending order
    - No duplicates exist in the result
    - Every element in result comes from the input array
    - Every distinct element from input appears in result
-/
theorem numpy_unique_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_unique arr
    ⦃⇓result => ⌜let m := result.1
                  let unique_arr := result.2
                  -- The result is sorted in ascending order
                  (∀ i j : Fin m, i < j → unique_arr.get i < unique_arr.get j) ∧
                  -- No duplicates in the result
                  (∀ i j : Fin m, i ≠ j → unique_arr.get i ≠ unique_arr.get j) ∧
                  -- Every element in result comes from the input array
                  (∀ i : Fin m, ∃ j : Fin n, unique_arr.get i = arr.get j) ∧
                  -- Every distinct element from input appears in result
                  (∀ i : Fin n, ∃ j : Fin m, arr.get i = unique_arr.get j)⌝⦄ := by
  sorry