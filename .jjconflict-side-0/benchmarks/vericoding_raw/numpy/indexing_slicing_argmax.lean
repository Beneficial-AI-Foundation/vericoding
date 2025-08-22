import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.argmax",
  "category": "Index finding",
  "description": "Returns the indices of the maximum values along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argmax.html",
  "doc": "Returns the indices of the maximum values along an axis.\n\nParameters\n----------\na : array_like\n    Input array.\naxis : int, optional\n    By default, the index is into the flattened array, otherwise along the specified axis.\nout : array, optional\n    If provided, the result will be inserted into this array.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nindex_array : ndarray of ints\n    Array of indices into the array. It has the same shape as ``a.shape`` with the dimension along `axis` removed.\n\nNotes\n-----\nIn case of multiple occurrences of the maximum values, the indices corresponding to the first occurrence are returned.",
  "code": "@array_function_dispatch(_argmax_dispatcher)\ndef argmax(a, axis=None, out=None, *, keepdims=np._NoValue):\n    \"\"\"\n    Returns the indices of the maximum values along an axis.\n\n    Parameters\n    ----------\n    a : array_like\n        Input array.\n    axis : int, optional\n        By default, the index is into the flattened array, otherwise\n        along the specified axis.\n    out : array, optional\n        If provided, the result will be inserted into this array. It should\n        be of the appropriate shape and dtype.\n    keepdims : bool, optional\n        If this is set to True, the axes which are reduced are left\n        in the result as dimensions with size one. With this option,\n        the result will broadcast correctly against the array.\n\n    Returns\n    -------\n    index_array : ndarray of ints\n        Array of indices into the array. It has the same shape as ``a.shape``\n        with the dimension along `axis` removed.\n\n    Notes\n    -----\n    In case of multiple occurrences of the maximum values, the indices\n    corresponding to the first occurrence are returned.\n    \"\"\"\n    kwds = {'keepdims': keepdims} if keepdims is not np._NoValue else {}\n    return _wrapfunc(a, 'argmax', axis=axis, out=out, **kwds)"
}
-/

open Std.Do

/-- Returns the index of the maximum value in a non-empty vector (first occurrence) -/
def argmax {n : Nat} (arr : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: argmax returns the index of the first maximum element
    This comprehensive specification captures:
    1. The returned index points to a maximum element
    2. All elements to the left of the returned index are strictly less than the maximum
    3. All elements to the right of the returned index are less than or equal to the maximum
    4. The function returns the first occurrence of the maximum value
    5. The returned index is valid (type-safe with Fin)
    6. The result is deterministic for the same input
-/
theorem argmax_spec {n : Nat} (arr : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax arr
    ⦃⇓idx => ⌜(∀ i : Fin (n + 1), arr.get i ≤ arr.get idx) ∧
             (∀ i : Fin (n + 1), i < idx → arr.get i < arr.get idx) ∧
             (∀ i : Fin (n + 1), idx < i → arr.get i ≤ arr.get idx) ∧
             (∀ j : Fin (n + 1), arr.get j = arr.get idx → idx ≤ j)⌝⦄ := by
  sorry