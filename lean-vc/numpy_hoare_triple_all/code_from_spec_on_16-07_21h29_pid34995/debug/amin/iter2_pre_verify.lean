import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.amin",
  "category": "Order statistics",
  "description": "Return the minimum of an array or minimum along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.amin.html",
  "doc": "numpy.amin(a, axis=None, out=None, keepdims=<no value>, initial=<no value>, where=<no value>)\n\nReturn the minimum of an array or minimum along an axis.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : None or int or tuple of ints, optional\n    Axis or axes along which to operate. By default, flattened input is used.\n    If this is a tuple of ints, the minimum is selected over multiple axes,\n    instead of a single axis or all the axes as before.\nout : ndarray, optional\n    Alternative output array in which to place the result. Must be of the same\n    shape and buffer length as the expected output.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result\n    as dimensions with size one. With this option, the result will broadcast\n    correctly against the input array.\ninitial : scalar, optional\n    The maximum value of an output element. Must be present to allow computation\n    on empty slice.\nwhere : array_like of bool, optional\n    Elements to compare for the minimum.\n\nReturns\n-------\namin : ndarray or scalar\n    Minimum of a. If axis is None, the result is a scalar value. If axis is given,\n    the result is an array of dimension a.ndim - 1.\n\nNotes\n-----\nNaN values are propagated, that is if at least one item is NaN, the corresponding\nmin value will be NaN as well. To ignore NaN values (MATLAB behavior), please use\nnanmin.\n\nDon't use amin for element-wise comparison of 2 arrays; when a.shape[0] is 2,\nminimum(a[0], a[1]) is faster than amin(a, axis=0).",
  "code": "# C implementation for performance\n# Return the minimum of an array or minimum along an axis\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: # C implementation in numpy/_core/src/multiarray/calculation.c\n# Python wrapper:\n@array_function_dispatch(_amin_dispatcher)\ndef amin(a, axis=None, out=None, keepdims=np._NoValue, initial=np._NoValue,\n         where=np._NoValue):\n    \"\"\"\n    Return the minimum of an array or minimum along an axis.\n    \n    \`amin\` is an alias of \`~numpy.min\`.\n    \n    See Also\n    --------\n    min : alias of this function\n    ndarray.min : equivalent method\n    nanmin : minimum that ignores NaN values\n    minimum : element-wise minimum of two arrays\n    fmin : element-wise minimum that propagates NaN\n    argmin : indices of minimum values\n    \"\"\"\n    return _wrapreduction(a, np.minimum, 'min', axis, None, out,\n                          keepdims=keepdims, initial=initial, where=where)"
}
-/

-- LLM HELPER
def vector_min_aux {n : Nat} (a : Vector Float (n + 1)) : Nat → Float
  | 0 => a.get 0
  | k + 1 => min (vector_min_aux a k) (a.get ⟨k + 1, Nat.succ_lt_succ_iff.mpr (Nat.lt_of_succ_le (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.le_refl _)))))⟩)

-- LLM HELPER
def vector_min {n : Nat} (a : Vector Float (n + 1)) : Float :=
  vector_min_aux a n

/-- numpy.amin: Return the minimum of an array or minimum along an axis.

    This is an alias for numpy.min that returns the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This is a reduction operation that finds the smallest value in the array.
    NaN values are propagated - if any element is NaN, the result will be NaN.
-/
def amin {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  pure (vector_min a)

-- LLM HELPER
lemma vector_min_aux_le {n : Nat} (a : Vector Float (n + 1)) (k : Nat) (i : Fin (n + 1)) (h : i.val ≤ k) :
    vector_min_aux a k ≤ a.get i := by
  induction k with
  | zero => 
    simp [vector_min_aux]
    have : i.val = 0 := Nat.eq_zero_of_le_zero h
    rw [← Fin.val_inj] at this
    simp [this]
  | succ k ih =>
    simp [vector_min_aux]
    cases' Nat.lt_or_eq_of_le h with h_lt h_eq
    · have h_le : i.val ≤ k := Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h_lt)
      exact le_trans (min_le_left _ _) (ih h_le)
    · have : i.val = k + 1 := h_eq
      rw [← this]
      exact min_le_right _ _

-- LLM HELPER
lemma vector_min_aux_exists {n : Nat} (a : Vector Float (n + 1)) (k : Nat) (h : k < n + 1) :
    ∃ i : Fin (n + 1), a.get i = vector_min_aux a k ∧ i.val ≤ k := by
  induction k with
  | zero => 
    simp [vector_min_aux]
    use 0
    simp
  | succ k ih =>
    simp [vector_min_aux]
    by_cases h_eq : vector_min_aux a k ≤ a.get ⟨k + 1, h⟩
    · have : min (vector_min_aux a k) (a.get ⟨k + 1, h⟩) = vector_min_aux a k := min_eq_left h_eq
      rw [this]
      have h_k : k < n + 1 := Nat.lt_of_succ_lt h
      obtain ⟨i, hi_eq, hi_le⟩ := ih h_k
      use i
      exact ⟨hi_eq, le_trans hi_le (Nat.le_succ k)⟩
    · have : min (vector_min_aux a k) (a.get ⟨k + 1, h⟩) = a.get ⟨k + 1, h⟩ := min_eq_right (le_of_not_le h_eq)
      rw [this]
      use ⟨k + 1, h⟩
      simp

/-- Specification: amin returns the minimum element in the vector.

    Precondition: True (non-empty constraint is enforced by type Vector Float (n + 1))
    Postcondition: result is the minimum value and is an element of the vector
    
    Properties:
    1. The result is actually an element of the input vector
    2. The result is less than or equal to all elements in the vector
    3. This captures the mathematical definition of minimum
-/
theorem amin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    amin a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  simp [amin, vector_min, triple_monad_pure]
  constructor
  · obtain ⟨i, hi_eq, _⟩ := vector_min_aux_exists a n (Nat.lt_succ_self n)
    use i
    exact hi_eq.symm
  · intro i
    exact vector_min_aux_le a n i (Nat.le_of_lt_succ i.isLt)