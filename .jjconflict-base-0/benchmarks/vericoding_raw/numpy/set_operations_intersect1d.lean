import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.intersect1d",
  "category": "Set operations",
  "description": "Find the intersection of two arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.intersect1d.html",
  "doc": "Find the intersection of two arrays.\n\nReturn the sorted, unique values that are in both of the input arrays.\n\nParameters\n----------\nar1, ar2 : array_like\n    Input arrays. Will be flattened if not already 1D.\nassume_unique : bool\n    If True, the input arrays are both assumed to be unique, which\n    can speed up the calculation.  If True but \`\`ar1\`\` or \`\`ar2\`\` are not\n    unique, incorrect results and out-of-bounds indices could result.\n    Default is False.\nreturn_indices : bool\n    If True, the indices which correspond to the intersection of the two\n    arrays are returned. The first instance of a value is used if there are\n    multiple. Default is False.\n\n    .. versionadded:: 1.15.0\n\nReturns\n-------\nintersect1d : ndarray\n    Sorted 1D array of common and unique elements.\ncomm1 : ndarray\n    The indices of the first occurrences of the common values in \`ar1\`.\n    Only provided if \`return_indices\` is True.\ncomm2 : ndarray\n    The indices of the first occurrences of the common values in \`ar2\`.\n    Only provided if \`return_indices\` is True.",
  "code": "def intersect1d(ar1, ar2, assume_unique=False, return_indices=False):\n    \"\"\"\n    Find the intersection of two arrays.\n\n    Return the sorted, unique values that are in both of the input arrays.\n\n    Parameters\n    ----------\n    ar1, ar2 : array_like\n        Input arrays. Will be flattened if not already 1D.\n    assume_unique : bool\n        If True, the input arrays are both assumed to be unique, which\n        can speed up the calculation.  If True but \`\`ar1\`\` or \`\`ar2\`\` are not\n        unique, incorrect results and out-of-bounds indices could result.\n        Default is False.\n    return_indices : bool\n        If True, the indices which correspond to the intersection of the two\n        arrays are returned. The first instance of a value is used if there are\n        multiple. Default is False.\n\n        .. versionadded:: 1.15.0\n\n    Returns\n    -------\n    intersect1d : ndarray\n        Sorted 1D array of common and unique elements.\n    comm1 : ndarray\n        The indices of the first occurrences of the common values in \`ar1\`.\n        Only provided if \`return_indices\` is True.\n    comm2 : ndarray\n        The indices of the first occurrences of the common values in \`ar2\`.\n        Only provided if \`return_indices\` is True.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> np.intersect1d([1, 3, 4, 3], [3, 1, 2, 1])\n    array([1, 3])\n\n    To intersect more than two arrays, use functools.reduce:\n\n    >>> from functools import reduce\n    >>> reduce(np.intersect1d, ([1, 3, 4, 3], [3, 1, 2, 1], [6, 3, 4, 2]))\n    array([3])\n\n    To return the indices of the values common to the input arrays\n    along with the intersected values:\n\n    >>> x = np.array([1, 1, 2, 3, 4])\n    >>> y = np.array([2, 1, 4, 6])\n    >>> xy, x_ind, y_ind = np.intersect1d(x, y, return_indices=True)\n    >>> x_ind, y_ind\n    (array([0, 2, 4]), array([1, 0, 2]))\n    >>> xy, x[x_ind], y[y_ind]\n    (array([1, 2, 4]), array([1, 2, 4]), array([1, 2, 4]))\n\n    \"\"\"\n    ar1 = np.asanyarray(ar1)\n    ar2 = np.asanyarray(ar2)\n\n    if not assume_unique:\n        if return_indices:\n            ar1, ind1 = unique(ar1, return_index=True)\n            ar2, ind2 = unique(ar2, return_index=True)\n        else:\n            ar1 = unique(ar1)\n            ar2 = unique(ar2)\n    else:\n        ar1 = ar1.ravel()\n        ar2 = ar2.ravel()\n\n    aux = np.concatenate((ar1, ar2))\n    if return_indices:\n        aux_sort_indices = np.argsort(aux, kind='mergesort')\n        aux = aux[aux_sort_indices]\n    else:\n        aux.sort()\n\n    mask = aux[1:] == aux[:-1]\n    int1d = aux[:-1][mask]\n\n    if return_indices:\n        ar1_indices = aux_sort_indices[:-1][mask]\n        ar2_indices = aux_sort_indices[1:][mask] - ar1.size\n        if not assume_unique:\n            ar1_indices = ind1[ar1_indices]\n            ar2_indices = ind2[ar2_indices]\n\n        return int1d, ar1_indices, ar2_indices\n    else:\n        return int1d"
}
-/

/-- Find the intersection of two arrays.
    Returns the sorted, unique values that are in both input arrays. -/
def intersect1d {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) : Id (Vector Int k) :=
  sorry

/-- Specification: intersect1d returns a sorted array of unique values 
    that exist in both input arrays -/
theorem intersect1d_spec {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) :
    ⦃⌜True⌝⦄
    intersect1d ar1 ar2
    ⦃⇓result => ⌜
      -- Result contains only values that exist in both arrays
      (∀ i : Fin k, ∃ j : Fin n, ∃ l : Fin m, 
        result.get i = ar1.get j ∧ result.get i = ar2.get l) ∧
      -- Result is sorted in ascending order
      (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
      -- Result contains unique values (no duplicates)
      (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
      -- Result is complete (contains all common values)
      (∀ val : Int, (∃ i : Fin n, ar1.get i = val) ∧ (∃ j : Fin m, ar2.get j = val) →
        ∃ l : Fin k, result.get l = val)
    ⌝⦄ := by
  sorry