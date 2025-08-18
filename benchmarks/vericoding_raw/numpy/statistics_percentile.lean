import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.percentile",
  "category": "Order statistics",
  "description": "Compute the q-th percentile of the data along the specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.percentile.html",
  "doc": "numpy.percentile(a, q, axis=None, out=None, overwrite_input=False, method='linear', keepdims=False, *, weights=None, interpolation=None)\n\nCompute the q-th percentile of the data along the specified axis.\n\nReturns the q-th percentile(s) of the array elements.\n\nParameters\n----------\na : array_like of real numbers\n    Input array or object that can be converted to an array.\nq : array_like of float\n    Percentile or sequence of percentiles to compute, which must be between 0 and 100 inclusive.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the percentiles are computed. The default is to compute the percentile(s) along a flattened version of the array.\nout : ndarray, optional\n    Alternative output array in which to place the result. It must have the same shape and buffer length as the expected output.\noverwrite_input : bool, optional\n    If True, then allow the input array a to be modified by intermediate calculations, to save memory.\nmethod : str, optional\n    This parameter specifies the method to use for estimating the percentile. Default is 'linear'.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nweights : array_like, optional\n    An array of weights associated with the values in a.\ninterpolation : str, optional\n    Deprecated name for the method keyword argument.\n\nReturns\n-------\npercentile : scalar or ndarray\n    If q is a single percentile and axis=None, then the result is a scalar. Otherwise, an array is returned.",
  "code": "# Implementation in numpy/lib/_function_base_impl.py\n@array_function_dispatch(_percentile_dispatcher)\ndef percentile(a,\n               q,\n               axis=None,\n               out=None,\n               overwrite_input=False,\n               method=\"linear\",\n               keepdims=False,\n               *,\n               weights=None,\n               interpolation=None):\n    \"\"\"\n    Compute the q-th percentile of the data along the specified axis.\n    \"\"\"\n    if interpolation is not None:\n        _raise_warning(interpolation, method)\n    \n    q = np.asanyarray(q)\n    if not _quantile_is_valid(q):\n        raise ValueError(\"Percentiles must be in the range [0, 100]\")\n    q = q / 100\n    \n    a = np.asanyarray(a)\n    if a.dtype.char in \"SUV\":  # strings/unicode/void\n        raise TypeError(\"a must be an array of numerical dtype\")\n    \n    return _quantile(a, q, axis, out, overwrite_input, method, keepdims,\n                     weights)"
}
-/

/-- Compute the q-th percentile of the data in a vector.
    For a sorted vector, the q-th percentile is the value below which q percent of the data falls.
    This implementation focuses on the fundamental mathematical definition of percentiles. -/
def percentile {n : Nat} (arr : Vector Float (n + 1)) (q : Float) : Id Float :=
  sorry

/-- Specification: percentile computes the q-th percentile value correctly.
    The percentile is defined as the value v such that at least q% of the data
    is less than or equal to v, and at least (100-q)% of the data is greater than or equal to v.
    
    Mathematical properties:
    1. The percentile value must be within the range of the data (or interpolated between values)
    2. Special cases: q=0 gives minimum, q=100 gives maximum
    3. The result is bounded by the minimum and maximum values in the array -/
theorem percentile_spec {n : Nat} (arr : Vector Float (n + 1)) (q : Float) 
    (h_valid_q : 0 ≤ q ∧ q ≤ 100) :
    ⦃⌜0 ≤ q ∧ q ≤ 100⌝⦄
    percentile arr q
    ⦃⇓result => ⌜
      -- The result is bounded by the minimum and maximum values in the array
      (∀ i : Fin (n + 1), arr.get i ≤ result → 
        ∃ j : Fin (n + 1), arr.get j ≥ result) ∧
      (∀ i : Fin (n + 1), arr.get i ≥ result → 
        ∃ j : Fin (n + 1), arr.get j ≤ result) ∧
      -- Special cases
      (q = 0 → ∀ i : Fin (n + 1), result ≤ arr.get i) ∧
      (q = 100 → ∀ i : Fin (n + 1), arr.get i ≤ result)
    ⌝⦄ := by
  sorry