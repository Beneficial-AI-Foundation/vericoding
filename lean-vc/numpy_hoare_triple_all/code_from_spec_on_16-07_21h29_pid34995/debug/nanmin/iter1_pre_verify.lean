import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.nanmin",
  "category": "Order statistics",
  "description": "Return minimum of an array or minimum along an axis, ignoring any NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanmin.html",
  "doc": "numpy.nanmin(a, axis=None, out=None, keepdims=<no value>, initial=<no value>, where=<no value>)\n\nReturn minimum of an array or minimum along an axis, ignoring any NaNs.\nWhen all-NaN slices are encountered a RuntimeWarning is raised and NaN is returned for that slice.\n\nParameters\n----------\na : array_like\n    Array containing numbers whose minimum is desired. If a is not an array, a conversion is attempted.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the minimum is computed. The default is to compute the minimum of the flattened array.\nout : ndarray, optional\n    Alternate output array in which to place the result. The default is None; if provided, it must have the same shape as the expected output.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\ninitial : scalar, optional\n    The maximum value of an output element. Must be present to allow computation on empty slice.\nwhere : array_like of bool, optional\n    Elements to compare for the minimum.\n\nReturns\n-------\nnanmin : ndarray\n    An array with the same shape as a, with the specified axis removed. If a is a 0-d array, or if axis is None, an ndarray scalar is returned.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanmin_dispatcher)\ndef nanmin(a, axis=None, out=None, keepdims=np._NoValue, initial=np._NoValue,\n           where=np._NoValue):\n    \"\"\"\n    Return minimum of an array or minimum along an axis, ignoring any NaNs.\n    \"\"\"\n    kwargs = {}\n    if initial is not np._NoValue:\n        kwargs['initial'] = initial\n    if where is not np._NoValue:\n        kwargs['where'] = where\n    if type(a) is not mu.ndarray:\n        try:\n            nanmin = a.nanmin\n        except AttributeError:\n            pass\n        else:\n            return nanmin(axis=axis, out=out, keepdims=keepdims, **kwargs)\n    return _nanextremum(np.min, a, axis, out, keepdims, initial, where)"
}
-/

-- LLM HELPER
def findNanMin (a : Vector Float (n + 1)) : Float :=
  let rec loop (i : Fin (n + 1)) (current_min : Option Float) : Float :=
    if i.val = 0 then
      let val := a.get i
      if val.isNaN then
        match current_min with
        | none => Float.nan
        | some min => min
      else
        match current_min with
        | none => val
        | some min => if val < min then val else min
    else
      let val := a.get i
      let next_min := 
        if val.isNaN then current_min
        else
          match current_min with
          | none => some val
          | some min => some (if val < min then val else min)
      loop ⟨i.val - 1, Nat.sub_lt i.val.succ_pos (Nat.succ_pos 0)⟩ next_min
  loop ⟨n, Nat.lt_succ_iff.mpr (Nat.le_refl n)⟩ none

/-- Returns the minimum value of all elements in a non-empty vector, ignoring NaN values.
    When all elements are NaN, returns NaN.
    
    Mathematical Properties:
    - Ignores NaN values in the computation
    - Returns the minimum of all non-NaN elements
    - If all elements are NaN, returns NaN
    - If at least one element is not NaN, returns the minimum non-NaN value
    - For vectors with no NaN values, behaves identically to regular min -/
def nanmin {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  pure (findNanMin a)

/-- Specification: nanmin returns the minimum value in the vector, ignoring NaN values.
    
    Mathematical properties:
    1. If there exists at least one non-NaN element, the result is the minimum among non-NaN elements
    2. If all elements are NaN, the result is NaN
    3. The result is either a non-NaN element from the vector or NaN
    4. For vectors without NaN values, nanmin behaves identically to regular min
    5. NaN values are completely ignored during the minimum computation
    6. Sanity check: result is either NaN or exists in the vector -/
theorem nanmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    nanmin a
    ⦃⇓result => ⌜-- Case 1: If there exists at least one non-NaN element
                 ((∃ i : Fin (n + 1), ¬result.isNaN ∧ ¬(a.get i).isNaN) →
                   (∃ min_idx : Fin (n + 1), 
                     result = a.get min_idx ∧ 
                     ¬(a.get min_idx).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
                 -- Case 2: If all elements are NaN, result is NaN
                 ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
                 -- Case 3: NaN values are ignored (result is min of non-NaN elements)
                 (¬result.isNaN → 
                   (∃ witness : Fin (n + 1), 
                     result = a.get witness ∧ 
                     ¬(a.get witness).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
                 -- Case 4: For vectors without NaN, behaves like regular min
                 ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
                   (∃ min_idx : Fin (n + 1),
                     result = a.get min_idx ∧
                     (∀ j : Fin (n + 1), result ≤ a.get j))) ∧
                 -- Sanity check: result is either NaN or exists in the vector
                 (result.isNaN ∨ (∃ witness : Fin (n + 1), result = a.get witness))⌝⦄ := by
  simp [nanmin]
  simp [Id.pure]
  simp [findNanMin]
  constructor
  · intro h
    sorry
  constructor
  · intro h
    sorry
  constructor
  · intro h
    sorry
  constructor
  · intro h
    sorry
  · sorry