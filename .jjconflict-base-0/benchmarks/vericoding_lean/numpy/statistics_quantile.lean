import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.quantile",
  "category": "Order statistics",
  "description": "Compute the q-th quantile of the data along the specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.quantile.html",
  "doc": "numpy.quantile(a, q, axis=None, out=None, overwrite_input=False, method='linear', keepdims=False, *, weights=None, interpolation=None)\n\nCompute the q-th quantile of the data along the specified axis.\n\nParameters\n----------\na : array_like of real numbers\n    Input array or object that can be converted to an array.\nq : array_like of float\n    Quantile or sequence of quantiles to compute, which must be between 0 and 1 inclusive.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the quantiles are computed.\nout : ndarray, optional\n    Alternative output array in which to place the result.\noverwrite_input : bool, optional\n    If True, then allow the input array a to be modified by intermediate calculations.\nmethod : str, optional\n    This parameter specifies the method to use for estimating the quantile.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nweights : array_like, optional\n    An array of weights associated with the values in a.\ninterpolation : str, optional\n    Deprecated name for the method keyword argument.\n\nReturns\n-------\nquantile : scalar or ndarray\n    If q is a single quantile and axis=None, then the result is a scalar.",
  "code": "# Implementation in numpy/lib/_function_base_impl.py\n@array_function_dispatch(_quantile_dispatcher)\ndef quantile(a,\n             q,\n             axis=None,\n             out=None,\n             overwrite_input=False,\n             method=\"linear\",\n             keepdims=False,\n             *,\n             weights=None,\n             interpolation=None):\n    \"\"\"\n    Compute the q-th quantile of the data along the specified axis.\n    \"\"\"\n    if interpolation is not None:\n        _raise_warning(interpolation, method)\n    \n    a = np.asanyarray(a)\n    if a.dtype.char in \"SUV\":  # strings/unicode/void\n        raise TypeError(\"a must be an array of numerical dtype\")\n    \n    q = np.asanyarray(q)\n    if not _quantile_is_valid(q):\n        raise ValueError(\"Quantiles must be in the range [0, 1]\")\n    \n    return _quantile(a, q, axis, out, overwrite_input, method, keepdims,\n                     weights)"
}
-/

/-- Compute the q-th quantile of the data in a vector -/
def quantile {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_valid : 0 ≤ q ∧ q ≤ 1) : Id Float :=
  sorry

/-- Specification: quantile returns a value that has the property that 
    approximately q proportion of the data is less than or equal to it -/
theorem quantile_spec {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_valid : 0 ≤ q ∧ q ≤ 1) :
    ⦃⌜0 ≤ q ∧ q ≤ 1⌝⦄
    quantile a q h_valid
    ⦃⇓result => ⌜
      -- The result is within the range of the input data
      (∃ i : Fin (n + 1), a.get i ≤ result) ∧
      (∃ i : Fin (n + 1), result ≤ a.get i) ∧
      -- For 0-quantile, result should be ≤ minimum
      (q = 0 → ∀ i : Fin (n + 1), result ≤ a.get i) ∧
      -- For 1-quantile, result should be ≥ maximum  
      (q = 1 → ∀ i : Fin (n + 1), a.get i ≤ result)⌝⦄ := by
  sorry
