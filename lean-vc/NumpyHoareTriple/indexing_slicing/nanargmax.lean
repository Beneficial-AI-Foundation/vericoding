import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.nanargmax",
  "category": "Index finding",
  "description": "Return the indices of the maximum values in the specified axis ignoring NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanargmax.html",
  "doc": "Return the indices of the maximum values in the specified axis ignoring NaNs.\n\nFor all-NaN slices \`\`ValueError\`\` is raised. Warning: the results cannot be trusted if a slice contains only NaNs and -Infs.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : int, optional\n    Axis along which to operate. By default flattened input is used.\nout : array, optional\n    If provided, the result will be inserted into this array.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nindex_array : ndarray\n    An array of indices or a single index value.",
  "code": "@array_function_dispatch(_nanargmax_dispatcher)\ndef nanargmax(a, axis=None, out=None, *, keepdims=np._NoValue):\n    \"\"\"\n    Return the indices of the maximum values in the specified axis ignoring\n    NaNs. For all-NaN slices \`\`ValueError\`\` is raised. Warning: the\n    results cannot be trusted if a slice contains only NaNs and -Infs.\n\n    Parameters\n    ----------\n    a : array_like\n        Input data.\n    axis : int, optional\n        Axis along which to operate.  By default flattened input is used.\n    out : array, optional\n        If provided, the result will be inserted into this array. It should\n        be of the appropriate shape and dtype.\n\n        .. versionadded:: 1.22.0\n    keepdims : bool, optional\n        If this is set to True, the axes which are reduced are left\n        in the result as dimensions with size one. With this option,\n        the result will broadcast correctly against the array.\n\n        .. versionadded:: 1.22.0\n\n    Returns\n    -------\n    index_array : ndarray\n        An array of indices or a single index value.\n\n    See Also\n    --------\n    argmax, nanargmin\n    \"\"\"\n    a, mask = _replace_nan(a, -np.inf)\n    if mask is not None and mask.size:\n        mask = np.all(mask, axis=axis)\n        if np.any(mask):\n            raise ValueError(\"All-NaN slice encountered\")\n    res = np.argmax(a, axis=axis, out=out, keepdims=keepdims)\n    return res"
}
-/

open Std.Do

/-- Returns the index of the maximum value in a non-empty vector, ignoring NaN values.
    
    This function finds the index of the maximum value among all non-NaN elements in the vector.
    Requires that at least one element is not NaN, otherwise it would raise an error.
    
    In case of multiple occurrences of the maximum values, the indices
    corresponding to the first occurrence are returned.
-/
def nanargmax {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: nanargmax returns the index of the first maximum element among non-NaN values.
    
    This comprehensive specification captures:
    1. The returned index points to an element that is not NaN
    2. The element at the returned index is the maximum among all non-NaN elements
    3. The function returns the first occurrence of the maximum value (among non-NaN elements)
    4. The returned index is valid (type-safe with Fin)
    5. The precondition ensures at least one element is not NaN
    6. All non-NaN elements are less than or equal to the maximum
    7. Among elements with the same maximum value, the first index is returned
-/
theorem nanargmax_spec {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) :
    ⦃⌜∃ i : Fin (n + 1), ¬(a.get i).isNaN⌝⦄
    nanargmax a h_not_all_nan
    ⦃⇓idx => ⌜¬(a.get idx).isNaN ∧ 
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ a.get idx) ∧
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j = a.get idx → idx ≤ j)⌝⦄ := by
  sorry