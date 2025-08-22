import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.nanargmax",
  "category": "Searching",
  "description": "Return the indices of the maximum values in the specified axis ignoring NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanargmax.html",
  "doc": "Return the indices of the maximum values in the specified axis ignoring\nNaNs. For all-NaN slices \`\`ValueError\`\` is raised. Warning: the results\ncannot be trusted if a slice contains only NaNs and -Infs.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : int, optional\n    Axis along which to operate. By default flattened input is used.\nout : array, optional\n    If provided, the result will be inserted into this array. It should\n    be of the appropriate shape and dtype.\n\n    .. versionadded:: 1.22.0\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left\n    in the result as dimensions with size one. With this option,\n    the result will broadcast correctly against the array.\n\n    .. versionadded:: 1.22.0\n\nReturns\n-------\nindex_array : ndarray\n    An array of indices or a single index value.",
  "code": "@array_function_dispatch(_nanargmax_dispatcher)\ndef nanargmax(a, axis=None, out=None, *, keepdims=np._NoValue):\n    \"\"\"\n    Return the indices of the maximum values in the specified axis ignoring\n    NaNs. For all-NaN slices \`\`ValueError\`\` is raised. Warning: the\n    results cannot be trusted if a slice contains only NaNs and -Infs.\n\n\n    Parameters\n    ----------\n    a : array_like\n        Input data.\n    axis : int, optional\n        Axis along which to operate. By default flattened input is used.\n    out : array, optional\n        If provided, the result will be inserted into this array. It should\n        be of the appropriate shape and dtype.\n\n        .. versionadded:: 1.22.0\n    keepdims : bool, optional\n        If this is set to True, the axes which are reduced are left\n        in the result as dimensions with size one. With this option,\n        the result will broadcast correctly against the array.\n\n        .. versionadded:: 1.22.0\n\n    Returns\n    -------\n    index_array : ndarray\n        An array of indices or a single index value.\n\n    See Also\n    --------\n    argmax, nanargmin\n\n    \"\"\"\n    a, mask = _replace_nan(a, -np.inf)\n    if mask is not None:\n        mask = np.all(mask, axis=axis)\n        if np.any(mask):\n            raise ValueError(\"All-NaN slice encountered\")\n    return argmax(a, axis=axis, out=out, keepdims=keepdims)"
}
-/

/-- numpy.nanargmax: Returns the index of the maximum value in a vector, ignoring NaN values.

    Returns the index of the maximum value among all non-NaN elements in the array.
    Requires that at least one element is not NaN, otherwise it would raise an error.
    
    In case of multiple occurrences of the maximum values, the indices
    corresponding to the first occurrence are returned.

    This function returns the position of the largest non-NaN element in the array.
-/
def nanargmax {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: numpy.nanargmax returns the index of the maximum non-NaN element.

    Precondition: At least one element is not NaN
    Postcondition: The element at the returned index is not NaN, is the maximum 
    among all non-NaN values, and is the first occurrence of such maximum value.
-/
theorem nanargmax_spec {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) :
    ⦃⌜∃ i : Fin (n + 1), ¬(a.get i).isNaN⌝⦄
    nanargmax a h_not_all_nan
    ⦃⇓idx => ⌜¬(a.get idx).isNaN ∧ 
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ a.get idx) ∧
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j = a.get idx → idx ≤ j)⌝⦄ := by
  sorry