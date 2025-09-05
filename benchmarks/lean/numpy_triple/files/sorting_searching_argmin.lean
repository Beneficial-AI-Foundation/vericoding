/- 
{
  "name": "numpy.argmin",
  "category": "Searching",
  "description": "Returns the indices of the minimum values along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argmin.html",
  "doc": "Returns the indices of the minimum values along an axis.\n\nParameters\n----------\na : array_like\n    Input array.\naxis : int, optional\n    By default, the index is into the flattened array, otherwise\n    along the specified axis.\nout : array, optional\n    If provided, the result will be inserted into this array. It should\n    be of the appropriate shape and dtype.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left\n    in the result as dimensions with size one. With this option,\n    the result will broadcast correctly against the input array.\n\n    If the default value is passed, then \`keepdims\` will not be\n    passed through to the \`argmin\` method of sub-classes of\n    \`ndarray\`, however any non-default value will be. If the\n    sub-class' method does not implement \`keepdims\` any\n    exceptions will be raised.\n\nReturns\n-------\nindex_array : ndarray of ints\n    Array of indices into the array. It has the same shape as \`a.shape\`\n    with the dimension along \`axis\` removed. If \`keepdims\` is set to True,\n    then the size of \`axis\` will be 1 with the resulting array having same\n    shape as \`a.shape\`.",
}
-/

/-  numpy.argmin: Returns the index of the minimum value.

    Returns the index of the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This function returns the position of the smallest element in the array.
    In case of multiple occurrences of the minimum values, the indices
    corresponding to the first occurrence are returned.
-/

/-  Specification: numpy.argmin returns the index of the minimum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the minimum value,
    and for ties, it returns the first occurrence.
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_argmin {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

theorem numpy_argmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmin a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get i ≤ a.get j) ∧ 
             (∀ j : Fin (n + 1), a.get j = a.get i → i ≤ j)⌝⦄ := by
  sorry
