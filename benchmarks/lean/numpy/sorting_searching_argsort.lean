import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.argsort",
  "category": "Sorting",
  "description": "Returns the indices that would sort an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argsort.html",
  "doc": "Returns the indices that would sort an array.\n\nPerform an indirect sort along the given axis using the algorithm specified\nby the \`kind\` keyword. It returns an array of indices of the same shape as\n\`a\` that index data along the given axis in sorted order.\n\nParameters\n----------\na : array_like\n    Array to sort.\naxis : int or None, optional\n    Axis along which to sort. The default is -1 (the last axis). If None,\n    the flattened array is used.\nkind : {'quicksort', 'mergesort', 'heapsort', 'stable'}, optional\n    Sorting algorithm. The default is 'quicksort'.\norder : str or list of str, optional\n    When \`a\` is an array with fields defined, this argument specifies\n    which fields to compare first, second, etc.\nstable : bool, optional\n    Sort stability. If \`\`True\`\`, the returned array will maintain\n    the relative order of \`\`a\`\` values which compare as equal.\n\nReturns\n-------\nindex_array : ndarray, int\n    Array of indices that sort \`a\` along the specified \`axis\`.\n    If \`a\` is one-dimensional, \`\`a[index_array]\`\` yields a sorted \`a\`.\n    More generally, \`\`take_along_axis(a, index_array, axis=axis)\`\`\n    always yields the sorted \`a\`, irrespective of dimensionality.",
  "code": "@array_function_dispatch(_argsort_dispatcher)\ndef argsort(a, axis=-1, kind=None, order=None, *, stable=None):\n    \"\"\"\n    Returns the indices that would sort an array.\n\n    Perform an indirect sort along the given axis using the algorithm specified\n    by the \`kind\` keyword. It returns an array of indices of the same shape as\n    \`a\` that index data along the given axis in sorted order.\n\n    Parameters\n    ----------\n    a : array_like\n        Array to sort.\n    axis : int or None, optional\n        Axis along which to sort. The default is -1 (the last axis). If None,\n        the flattened array is used.\n    kind : {'quicksort', 'mergesort', 'heapsort', 'stable'}, optional\n        Sorting algorithm. The default is 'quicksort'. Note that both 'stable'\n        and 'mergesort' use timsort or radix sort under the covers and, in general,\n        the actual implementation will vary with data type. The 'mergesort' option\n        is retained for backwards compatibility.\n\n        .. versionchanged:: 1.15.0.\n           The 'stable' option was added.\n\n    order : str or list of str, optional\n        When \`a\` is an array with fields defined, this argument specifies\n        which fields to compare first, second, etc. A single field can\n        be specified as a string, and not all fields need be specified,\n        but unspecified fields will still be used, in the order in which\n        they come up in the dtype, to break ties.\n    stable : bool, optional\n        Sort stability. If \`\`True\`\`, the returned array will maintain\n        the relative order of \`\`a\`\` values which compare as equal.\n        If \`\`False\`\` or \`\`None\`\`, this is not guaranteed. Internally,\n        this option selects \`\`kind='stable'\`\`. Default: \`\`None\`\`.\n\n        .. versionadded:: 2.0.0\n\n    Returns\n    -------\n    index_array : ndarray, int\n        Array of indices that sort \`a\` along the specified \`axis\`.\n        If \`a\` is one-dimensional, \`\`a[index_array]\`\` yields a sorted \`a\`.\n        More generally, \`\`take_along_axis(a, index_array, axis=axis)\`\`\n        always yields the sorted \`a\`, irrespective of dimensionality.\n\n    See Also\n    --------\n    sort : Describes sorting algorithms used.\n    lexsort : Indirect stable sort with multiple keys.\n    ndarray.sort : Inplace sort.\n    argpartition : Indirect partial sort.\n    take_along_axis : Apply \`\`index_array\`\` from argsort\n                      to an array as if by calling sort.\n\n    \"\"\"\n    return _wrapfunc(a, 'argsort', axis=axis, kind=kind, order=order,\n                     stable=stable)"
}
-/

/-- Returns the indices that would sort a vector in ascending order -/
def argsort {n : Nat} (a : Vector Float n) : Id (Vector (Fin n) n) :=
  sorry

/-- Specification: argsort returns indices that sort the input array -/
theorem argsort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    argsort a
    ⦃⇓indices => ⌜-- The result is a permutation of all indices
                   (∀ i : Fin n, ∃ j : Fin n, indices.get j = i) ∧
                   (∀ i j : Fin n, indices.get i = indices.get j → i = j) ∧
                   -- The indices produce a sorted sequence
                   (∀ i j : Fin n, i < j → a.get (indices.get i) ≤ a.get (indices.get j)) ∧
                   -- For equal elements, maintain relative order (stable sort)
                   (∀ i j : Fin n, i < j → a.get (indices.get i) = a.get (indices.get j) → indices.get i < indices.get j)⌝⦄ := by
  sorry