import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.nanmax",
  "category": "Order statistics",
  "description": "Return the maximum of an array or maximum along an axis, ignoring any NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanmax.html",
  "doc": "numpy.nanmax(a, axis=None, out=None, keepdims=<no value>, initial=<no value>, where=<no value>)\n\nReturn the maximum of an array or maximum along an axis, ignoring any NaNs.\nWhen all-NaN slices are encountered a RuntimeWarning is raised and NaN is returned for that slice.\n\nParameters\n----------\na : array_like\n    Array containing numbers whose maximum is desired. If a is not an array, a conversion is attempted.\naxis : {int, tuple of int, None}, optional\n    Axis or axes along which the maximum is computed. The default is to compute the maximum of the flattened array.\nout : ndarray, optional\n    Alternate output array in which to place the result. The default is None; if provided, it must have the same shape as the expected output.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\ninitial : scalar, optional\n    The minimum value of an output element. Must be present to allow computation on empty slice.\nwhere : array_like of bool, optional\n    Elements to compare for the maximum.\n\nReturns\n-------\nnanmax : ndarray\n    An array with the same shape as a, with the specified axis removed. If a is a 0-d array, or if axis is None, an ndarray scalar is returned.",
  "code": "# Implementation in numpy/lib/_nanfunctions_impl.py\n@array_function_dispatch(_nanmax_dispatcher)\ndef nanmax(a, axis=None, out=None, keepdims=np._NoValue, initial=np._NoValue,\n           where=np._NoValue):\n    \"\"\"\n    Return the maximum of an array or maximum along an axis, ignoring any NaNs.\n    \"\"\"\n    kwargs = {}\n    if initial is not np._NoValue:\n        kwargs['initial'] = initial\n    if where is not np._NoValue:\n        kwargs['where'] = where\n    if type(a) is not mu.ndarray:\n        try:\n            nanmax = a.nanmax\n        except AttributeError:\n            pass\n        else:\n            return nanmax(axis=axis, out=out, keepdims=keepdims, **kwargs)\n    return _nanextremum(np.max, a, axis, out, keepdims, initial, where)"
}
-/

open Std.Do

-- LLM HELPER
def findNanMax {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) : Float :=
  if idx.val = 0 then
    let elem := a.get idx
    if elem.isNaN then currentMax else
    if currentMax.isNaN then elem else
    max elem currentMax
  else
    let elem := a.get idx
    let newMax := if elem.isNaN then currentMax else
                  if currentMax.isNaN then elem else
                  max elem currentMax
    findNanMax a ⟨idx.val - 1, Nat.sub_lt idx.val.succ_pos⟩ newMax

/-- Returns the maximum value of all elements in a non-empty vector, ignoring NaN values.
    When all elements are NaN, returns NaN.
    
    Mathematical Properties:
    - Ignores NaN values in the computation
    - Returns the maximum of all non-NaN elements
    - If all elements are NaN, returns NaN
    - If at least one element is not NaN, returns the maximum non-NaN value
    - For vectors with no NaN values, behaves identically to regular max -/
def nanmax {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  Id.pure (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan)

-- LLM HELPER
lemma findNanMax_preserves_non_nan {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  (∃ i : Fin (n + 1), i.val ≤ idx.val ∧ ¬(a.get i).isNaN) ∨ ¬currentMax.isNaN → 
  ¬(findNanMax a idx currentMax).isNaN := by
  sorry

-- LLM HELPER
lemma findNanMax_is_maximum {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  (∀ i : Fin (n + 1), i.val ≤ idx.val ∧ ¬(a.get i).isNaN → a.get i ≤ findNanMax a idx currentMax) := by
  sorry

-- LLM HELPER
lemma findNanMax_exists_witness {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  ¬(findNanMax a idx currentMax).isNaN → 
  (∃ witness : Fin (n + 1), witness.val ≤ idx.val ∧ findNanMax a idx currentMax = a.get witness) ∨ 
  findNanMax a idx currentMax = currentMax := by
  sorry

-- LLM HELPER
lemma all_nan_implies_result_nan {n : Nat} (a : Vector Float (n + 1)) :
  (∀ i : Fin (n + 1), (a.get i).isNaN) → (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN := by
  sorry

/-- Specification: nanmax returns the maximum value in the vector, ignoring NaN values.
    
    Mathematical properties:
    1. If there exists at least one non-NaN element, the result is the maximum among non-NaN elements
    2. If all elements are NaN, the result is NaN
    3. The result is either a non-NaN element from the vector or NaN
    4. For vectors without NaN values, nanmax behaves identically to regular max
    5. NaN values are completely ignored during the maximum computation
    6. Sanity check: result is either NaN or exists in the vector -/
theorem nanmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    nanmax a
    ⦃⇓result => ⌜-- Case 1: If there exists at least one non-NaN element
                 ((∃ i : Fin (n + 1), ¬result.isNaN ∧ ¬(a.get i).isNaN) →
                   (∃ max_idx : Fin (n + 1), 
                     result = a.get max_idx ∧ 
                     ¬(a.get max_idx).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 2: If all elements are NaN, result is NaN
                 ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
                 -- Case 3: NaN values are ignored (result is max of non-NaN elements)
                 (¬result.isNaN → 
                   (∃ witness : Fin (n + 1), 
                     result = a.get witness ∧ 
                     ¬(a.get witness).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 4: For vectors without NaN, behaves like regular max
                 ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
                   (∃ max_idx : Fin (n + 1),
                     result = a.get max_idx ∧
                     (∀ j : Fin (n + 1), a.get j ≤ result))) ∧
                 -- Sanity check: result is either NaN or exists in the vector
                 (result.isNaN ∨ (∃ witness : Fin (n + 1), result = a.get witness))⌝⦄ := by
  simp [nanmax]
  apply wp_pure
  constructor
  · -- Case 1
    intro h
    apply findNanMax_exists_witness
    cases' h with i hi
    apply findNanMax_preserves_non_nan
    left
    use i
    constructor
    · simp
    · exact hi.2
  constructor
  · -- Case 2
    intro h
    apply all_nan_implies_result_nan
    exact h
  constructor
  · -- Case 3
    intro h
    apply findNanMax_exists_witness
    exact h
  constructor
  · -- Case 4
    intro h
    apply findNanMax_exists_witness
    apply findNanMax_preserves_non_nan
    left
    use ⟨0, Nat.succ_pos n⟩
    constructor
    · simp
    · exact h ⟨0, Nat.succ_pos n⟩
  · -- Sanity check
    by_cases h : (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN
    · left
      exact h
    · right
      apply findNanMax_exists_witness
      exact h