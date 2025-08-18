import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.nanmedian",
  "category": "Averages and variances",
  "description": "Compute the median along the specified axis, ignoring NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanmedian.html",
  "doc": "numpy.nanmedian(a, axis=None, out=None, overwrite_input=False, keepdims=False)\n\nCompute the median along the specified axis, while ignoring NaNs.\n\nReturns the median of the array elements.\n\nParameters\n----------\na : array_like\n    Input array or object that can be converted to an array.\naxis : {int, sequence of int, None}, optional\n    Axis or axes along which the medians are computed. The default is to compute the median along a flattened version of the array.\nout : ndarray, optional\n    Alternative output array in which to place the result. It must have the same shape and buffer length as the expected output.\noverwrite_input : bool, optional\n    If True, then allow use of memory of input array a for calculations. The input array will be modified by the call to median.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nmedian : ndarray\n    A new array holding the result. If the input contains integers or floats smaller than float64, then the output data-type is np.float64. Otherwise, the data-type of the output is the same as that of the input.\n\nNotes\n-----\nGiven a vector V of length N, the median of V is the middle value of a sorted copy of V, V_sorted - i.e., V_sorted[(N-1)/2], when N is odd, and the average of the two middle values of V_sorted when N is even.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanmedian_dispatcher)\ndef nanmedian(a, axis=None, out=None, overwrite_input=False, keepdims=False):\n    \"\"\"\n    Compute the median along the specified axis, while ignoring NaNs.\n    \"\"\"\n    a = np.asanyarray(a)\n    # apply_along_axis in _nanmedian doesn't handle empty arrays well,\n    # so deal them upfront\n    if a.size == 0:\n        return np.nanmean(a, axis, out=out, keepdims=keepdims)\n    \n    return function_base._ureduce(a, func=_nanmedian, keepdims=keepdims,\n                                  axis=axis, out=out,\n                                  overwrite_input=overwrite_input)\n\ndef _nanmedian(a, axis=None, out=None, overwrite_input=False):\n    \"\"\"\n    Private function that doesn't support extended axis or keepdims.\n    These extended features are handled by _ureduce.\n    \"\"\"\n    if axis is None or a.ndim == 1:\n        part = a.ravel()\n        if out is None:\n            return _nanmedian1d(part, overwrite_input)\n        else:\n            out[...] = _nanmedian1d(part, overwrite_input)\n            return out\n    else:\n        # for small medians use sort + indexing which is still faster than\n        # apply_along_axis\n        # benchmarked with shuffled (50, 50, x) median axis=2\n        if a.shape[axis] < 600:\n            return _nanmedian_small(a, axis, out, overwrite_input)\n        result = np.apply_along_axis(_nanmedian1d, axis, a, overwrite_input)\n        if out is not None:\n            out[...] = result\n        return result"
}
-/

open Std.Do

/-- Compute the median along the specified axis, ignoring NaNs.
    Returns the median of the array elements.
    For a vector V of length N, the median is the middle value of a sorted copy of V
    (ignoring NaN values), when N is odd, and the average of the two middle values when N is even.
    If all values are NaN, returns NaN. -/
def nanmedian {n : Nat} (a : Vector Float n) : Id Float :=
  sorry

/-- Specification: nanmedian computes the median of non-NaN values in the array.
    The result is NaN if all values are NaN, otherwise it's the median of the finite values.
    The median is defined as the middle value (for odd number of elements) or the average
    of two middle values (for even number of elements) when the non-NaN values are sorted. -/
theorem nanmedian_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nanmedian a
    ⦃⇓result => ⌜
      -- Case 1: All values are NaN
      (∀ i : Fin n, (a.get i).isNaN) → result.isNaN ∧
      -- Case 2: At least one finite value exists
      (∃ i : Fin n, ¬(a.get i).isNaN) → 
        ∃ finite_indices : List (Fin n),
          -- finite_indices contains all indices with finite values
          (∀ i : Fin n, i ∈ finite_indices ↔ ¬(a.get i).isNaN) ∧
          finite_indices.length > 0 ∧
          -- There exists a sorted permutation of finite values
          ∃ sorted_vals : List Float,
            -- sorted_vals is the sorted list of finite values
            sorted_vals.length = finite_indices.length ∧
            (∀ i : Fin finite_indices.length, 
              sorted_vals.get ⟨i, sorry⟩ = a.get (finite_indices.get ⟨i, sorry⟩)) ∧
            -- sorted_vals is in non-decreasing order
            (∀ i j : Fin sorted_vals.length, i < j → 
              sorted_vals.get ⟨i, sorry⟩ ≤ sorted_vals.get ⟨j, sorry⟩) ∧
            -- result is the median of sorted finite values
            (if sorted_vals.length % 2 = 1 then
              result = sorted_vals.get ⟨sorted_vals.length / 2, sorry⟩
            else
              result = (sorted_vals.get ⟨sorted_vals.length / 2 - 1, sorry⟩ + 
                       sorted_vals.get ⟨sorted_vals.length / 2, sorry⟩) / 2)
    ⌝⦄ := by
  sorry
