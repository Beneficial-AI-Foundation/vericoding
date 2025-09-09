/- 
{
  "name": "numpy.nanquantile",
  "category": "Order statistics",
  "description": "Compute the q-th quantile of the data along the specified axis, ignoring nan values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanquantile.html",
  "doc": "numpy.nanquantile(a, q, axis=None, out=None, overwrite_input=False, method='linear', keepdims=False, *, weights=None, interpolation=None)\n\nCompute the q-th quantile of the data along the specified axis, ignoring nan values.\n\nReturns the q-th quantile(s) of the array elements.\n\nParameters\n----------\na : array_like\n    Input array or object that can be converted to an array, containing nan values to be ignored.\nq : array_like of float\n    Quantile or sequence of quantiles to compute, which must be between 0 and 1 inclusive.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the quantiles are computed.\nout : ndarray, optional\n    Alternative output array in which to place the result.\noverwrite_input : bool, optional\n    If True, then allow the input array a to be modified by intermediate calculations.\nmethod : str, optional\n    Method to use for estimating the quantile.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\nweights : array_like, optional\n    An array of weights associated with the values in a.\ninterpolation : str, optional\n    Deprecated name for the method keyword argument.\n\nReturns\n-------\nquantile : scalar or ndarray\n    If q is a single quantile and axis=None, then the result is a scalar.",
}
-/

/-  Compute the q-th quantile of the data in a vector, ignoring NaN values.
    When all elements are NaN, returns NaN.

    Mathematical Properties:
    - Ignores NaN values in the computation
    - Returns the q-th quantile of all non-NaN elements 
    - If all elements are NaN, returns NaN
    - If at least one element is not NaN, returns the quantile of non-NaN values
    - For q=0, returns the minimum of non-NaN elements
    - For q=1, returns the maximum of non-NaN elements
    - For vectors with no NaN values, behaves identically to regular quantile -/

/-  Specification: nanquantile returns the q-th quantile of non-NaN values in the vector.

    Mathematical properties:
    1. The quantile parameter q must be between 0 and 1 inclusive
    2. If there exists at least one non-NaN element, the result is the q-th quantile among non-NaN elements
    3. If all elements are NaN, the result is NaN
    4. For q=0, result is the minimum of non-NaN elements
    5. For q=1, result is the maximum of non-NaN elements
    6. The result is bounded by the range of non-NaN elements
    7. NaN values are completely ignored during the quantile computation
    8. For vectors without NaN values, nanquantile behaves identically to regular quantile -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def nanquantile {n : Nat} (a : Vector Float (n + 1)) (q : Float) : Id Float :=
  sorry

theorem nanquantile_spec {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_q_valid : 0 ≤ q ∧ q ≤ 1) :
    ⦃⌜0 ≤ q ∧ q ≤ 1⌝⦄
    nanquantile a q
    ⦃⇓result => 
      ⌜-- Case 1: If there exists at least one non-NaN element
       ((∃ i : Fin (n + 1), ¬(a.get i).isNaN) →
         (¬result.isNaN ∧
          -- Result is bounded by the non-NaN elements
          (∃ min_idx : Fin (n + 1), ¬(a.get min_idx).isNaN ∧ 
            (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get min_idx ≤ a.get j) ∧
            a.get min_idx ≤ result) ∧
          (∃ max_idx : Fin (n + 1), ¬(a.get max_idx).isNaN ∧ 
            (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ a.get max_idx) ∧
            result ≤ a.get max_idx))) ∧
       -- Case 2: If all elements are NaN, result is NaN
       ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
       -- Case 3: For q=0, result is the minimum of non-NaN elements
       (q = 0 → (∃ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (∃ min_idx : Fin (n + 1), 
           result = a.get min_idx ∧ 
           ¬(a.get min_idx).isNaN ∧
           (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
       -- Case 4: For q=1, result is the maximum of non-NaN elements
       (q = 1 → (∃ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (∃ max_idx : Fin (n + 1), 
           result = a.get max_idx ∧ 
           ¬(a.get max_idx).isNaN ∧
           (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
       -- Case 5: For vectors without NaN, behaves like regular quantile
       ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (¬result.isNaN ∧
          (∃ lower_idx upper_idx : Fin (n + 1),
            a.get lower_idx ≤ result ∧ result ≤ a.get upper_idx)))⌝⦄ := by
  sorry
