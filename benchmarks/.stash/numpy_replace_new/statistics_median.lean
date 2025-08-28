import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic

/-!
{
  "name": "numpy.median",
  "category": "Averages and variances",
  "description": "Compute the median along the specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.median.html",
  "doc": "numpy.median(a, axis=None, out=None, overwrite_input=False, keepdims=False)\n\nCompute the median along the specified axis.\n\nReturns the median of the array elements.\n\nParameters\n----------\na : array_like\n    Input array or object that can be converted to an array.\naxis : {int, sequence of int, None}, optional\n    Axis or axes along which the medians are computed. The default is to compute the median along a flattened version of the array.\nout : ndarray, optional\n    Alternative output array in which to place the result. It must have the same shape and buffer length as the expected output.\noverwrite_input : bool, optional\n    If True, then allow use of memory of input array a for calculations. The input array will be modified by the call to median.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nmedian : ndarray\n    A new array holding the result. If the input contains integers or floats smaller than float64, then the output data-type is np.float64. Otherwise, the data-type of the output is the same as that of the input.\n\nNotes\n-----\nGiven a vector V of length N, the median of V is the middle value of a sorted copy of V, V_sorted - i.e., V_sorted[(N-1)/2], when N is odd, and the average of the two middle values of V_sorted when N is even.",
  "code": "# Implementation in numpy/lib/_function_base_impl.py\n@array_function_dispatch(_median_dispatcher)\ndef median(a, axis=None, out=None, overwrite_input=False, keepdims=False):\n    \"\"\"\n    Compute the median along the specified axis.\n    \"\"\"\n    return _ureduce(a, func=_median, keepdims=keepdims, axis=axis, out=out,\n                    overwrite_input=overwrite_input)\n\ndef _median(a, axis=None, out=None, overwrite_input=False):\n    # can't be reasonably be implemented in terms of percentile as we have\n    # to call mean to not break astropy\n    a = np.asanyarray(a)\n    \n    # Set the partition indexes\n    if axis is None:\n        sz = a.size\n    else:\n        sz = a.shape[axis]\n    if sz % 2 == 0:\n        szh = sz // 2\n        kth = [szh - 1, szh]\n    else:\n        kth = [(sz - 1) // 2]\n    \n    # Check if the array contains any nan's\n    if np.issubdtype(a.dtype, np.inexact):\n        kth.append(-1)\n    \n    if overwrite_input:\n        if axis is None:\n            part = a.ravel()\n            part.partition(kth)\n        else:\n            a.partition(kth, axis=axis)\n            part = a\n    else:\n        part = partition(a, kth, axis=axis)\n    \n    if part.shape == ():\n        # make 0-D arrays work\n        return part.item()\n    if axis is None:\n        axis = 0\n    \n    indexer = [slice(None)] * part.ndim\n    index = part.shape[axis] // 2\n    if part.shape[axis] % 2 == 1:\n        # index with slice to allow mean (below) to work\n        indexer[axis] = slice(index, index+1)\n    else:\n        indexer[axis] = slice(index-1, index+1)\n    indexer = tuple(indexer)\n    \n    # Check if the array contains any nan's\n    if np.issubdtype(a.dtype, np.inexact) and sz > 0:\n        # warn and return nans like mean would\n        rout = mean(part[indexer], axis=axis, out=out)\n        return np.lib._utils._median_nancheck(part, rout, axis)\n    else:\n        # if there are no nans\n        # Use mean in odd and even case to coerce data type,\n        # using out array if needed.\n        rout = mean(part[indexer], axis=axis, out=out)\n        return rout"
}
-/

open Std.Do

/-- Compute the median of a vector.
    For odd-length vectors, returns the middle value of the sorted array.
    For even-length vectors, returns the average of the two middle values. -/
def median {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry

/-- Specification: median returns the middle value(s) of a sorted vector.
    - For odd length (n+1), the median is the middle element when sorted
    - For even length (n+1), the median is the average of the two middle elements when sorted
    - The median divides the data such that approximately half the values are ≤ it,
      and approximately half are ≥ it -/
theorem median_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    median a
    ⦃⇓m => ⌜∃ sorted : Vector Float (n + 1),
            -- sorted is a permutation of a
            (∀ i : Fin (n + 1), ∃ j : Fin (n + 1), sorted.get i = a.get j) ∧
            (∀ j : Fin (n + 1), ∃ i : Fin (n + 1), sorted.get i = a.get j) ∧
            -- sorted is in non-decreasing order
            (∀ i j : Fin (n + 1), i < j → sorted.get i ≤ sorted.get j) ∧
            -- m is the median of sorted based on odd/even length
            (if h : (n + 1) % 2 = 1 then
              -- odd case: middle element at index n/2
              m = sorted.get ⟨n / 2, by
                have : n / 2 < n + 1 :=
  sorry
                exact this⟩
            else
              -- even case: average of two middle elements  
              m = (sorted.get ⟨n / 2, by
                have : n / 2 < n + 1 :=
  sorry
                exact this⟩ + 
                   sorted.get ⟨(n + 1) / 2, by
                have : (n + 1) / 2 < n + 1 :=
  sorry
                exact this⟩) / 2) ∧
            -- median property: it's a value that appears in the original vector
            -- or can be computed from values in the vector
            (∃ i : Fin (n + 1), m = sorted.get i ∨ 
             ∃ i j : Fin (n + 1), m = (sorted.get i + sorted.get j) / 2)⌝⦄ := by
  sorry