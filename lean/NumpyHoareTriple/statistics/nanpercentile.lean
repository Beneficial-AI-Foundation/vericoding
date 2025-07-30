import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.nanpercentile",
  "category": "Order statistics",
  "description": "Compute the q-th percentile of the data along the specified axis, ignoring nan values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanpercentile.html",
  "doc": "numpy.nanpercentile(a, q, axis=None, out=None, overwrite_input=False, method='linear', keepdims=False, *, weights=None, interpolation=None)\n\nCompute the q-th percentile of the data along the specified axis, ignoring nan values.\n\nReturns the q-th percentile(s) of the array elements.\n\nParameters\n----------\na : array_like\n    Input array or object that can be converted to an array, containing nan values to be ignored.\nq : array_like of float\n    Percentile or sequence of percentiles to compute, which must be between 0 and 100 inclusive.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the percentiles are computed.\nout : ndarray, optional\n    Alternative output array in which to place the result.\noverwrite_input : bool, optional\n    If True, then allow the input array a to be modified by intermediate calculations.\nmethod : str, optional\n    Method to use for estimating the percentile.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nweights : array_like, optional\n    An array of weights associated with the values in a.\ninterpolation : str, optional\n    Deprecated name for the method keyword argument.\n\nReturns\n-------\npercentile : scalar or ndarray\n    If q is a single percentile and axis=None, then the result is a scalar. Otherwise, an array is returned.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanpercentile_dispatcher)\ndef nanpercentile(a,\n                  q,\n                  axis=None,\n                  out=None,\n                  overwrite_input=False,\n                  method=\"linear\",\n                  keepdims=np._NoValue,\n                  *,\n                  weights=None,\n                  interpolation=None):\n    \"\"\"\n    Compute the q-th percentile of the data along the specified axis,\n    ignoring nan values.\n    \"\"\"\n    if interpolation is not None:\n        _raise_warning(interpolation, method)\n    \n    a = np.asanyarray(a)\n    if a.dtype.char in \"SUV\":  # strings/unicode/void\n        raise TypeError(\"a must be an array of numerical dtype\")\n    \n    q = np.asanyarray(q)\n    if not _quantile_is_valid(q):\n        raise ValueError(\"Percentiles must be in the range [0, 100]\")\n    q = q / 100.0\n    \n    return _nanquantile(a, q, axis, out, overwrite_input, method, keepdims,\n                        weights)"
}
-/

open Std.Do

/-- Compute the q-th percentile of the data along the specified axis, ignoring NaN values.
    Returns the q-th percentile of the array elements.
    If all values are NaN, returns NaN.
    The percentile q must be between 0 and 100 inclusive. -/
def nanpercentile {n : Nat} (a : Vector Float n) (q : Float) (h : 0 ≤ q ∧ q ≤ 100) : Id Float :=
  sorry

/-- Specification: nanpercentile computes the q-th percentile of non-NaN values in the array.
    The result is NaN if all values are NaN, otherwise it's the q-th percentile of the finite values.
    The percentile is computed by sorting the non-NaN values and finding the value at the position
    corresponding to the percentile q (between 0 and 100). -/
theorem nanpercentile_spec {n : Nat} (a : Vector Float n) (q : Float) (h : 0 ≤ q ∧ q ≤ 100) :
    ⦃⌜0 ≤ q ∧ q ≤ 100⌝⦄
    nanpercentile a q h
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
            -- Percentile computation: q% of sorted values
            (if sorted_vals.length = 1 then
               -- Single value case
               result = sorted_vals.get ⟨0, sorry⟩
             else
               -- For any percentile q, the result should be within the range
               -- of the sorted values and satisfy the percentile property
               ∃ idx : Nat, 
                 idx < sorted_vals.length ∧
                 result = sorted_vals.get ⟨idx, sorry⟩ ∨
                 -- OR result is an interpolated value between two consecutive elements
                 (∃ i j : Nat, 
                   i < sorted_vals.length ∧ j < sorted_vals.length ∧
                   i + 1 = j ∧
                   sorted_vals.get ⟨i, sorry⟩ ≤ result ∧
                   result ≤ sorted_vals.get ⟨j, sorry⟩)) ∧
            -- Sanity checks: result should be within bounds of finite values
            (¬result.isNaN → 
              sorted_vals.get ⟨0, sorry⟩ ≤ result ∧ 
              result ≤ sorted_vals.get ⟨sorted_vals.length - 1, sorry⟩)
    ⌝⦄ := by
  sorry
