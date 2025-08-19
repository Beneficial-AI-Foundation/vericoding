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

-- LLM HELPER
def Vector.toList {α : Type*} {n : Nat} (v : Vector α n) : List α :=
  v.val

-- LLM HELPER
def list_minimum (l : List Float) : Float :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => min x (list_minimum xs)

-- LLM HELPER
def list_maximum (l : List Float) : Float :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max x (list_maximum xs)

-- LLM HELPER
def Vector.get_min {n : Nat} (arr : Vector Float (n + 1)) : Float :=
  list_minimum arr.toList

-- LLM HELPER
def Vector.get_max {n : Nat} (arr : Vector Float (n + 1)) : Float :=
  list_maximum arr.toList

-- LLM HELPER
def Vector.sort {n : Nat} (arr : Vector Float (n + 1)) : Vector Float (n + 1) :=
  ⟨(arr.toList.mergeSort (· ≤ ·)).toArray, by simp [Vector.toList]; rw [List.toArray_toList]; exact arr.property⟩

-- LLM HELPER
def Float.toInt (x : Float) : Int :=
  Int.floor x

-- LLM HELPER
def Float.toNat (x : Float) : Nat :=
  Int.natAbs (Int.floor x)

-- LLM HELPER
def Int.toFloat (x : Int) : Float :=
  Float.ofInt x

-- LLM HELPER
instance : DecidableEq Float := by
  exact Classical.decidableEq

/-- Compute the q-th percentile of the data in a vector.
    For a sorted vector, the q-th percentile is the value below which q percent of the data falls.
    This implementation focuses on the fundamental mathematical definition of percentiles. -/
def percentile {n : Nat} (arr : Vector Float (n + 1)) (q : Float) : Id Float :=
  if q = 0 then
    pure (arr.get_min)
  else if q = 100 then
    pure (arr.get_max)
  else
    let sorted := arr.sort
    let position := (q / 100) * (n.toFloat)
    let idx := Float.toInt position
    let frac := position - (idx.toFloat)
    
    if idx < 0 then
      pure (sorted.get ⟨0, Nat.zero_lt_succ n⟩)
    else if Int.natAbs idx >= n then
      pure (sorted.get ⟨n, Nat.lt_succ_self n⟩)
    else
      let lower_idx := Int.natAbs idx
      let upper_idx := if lower_idx < n then lower_idx + 1 else lower_idx
      let lower_val := sorted.get ⟨lower_idx, by
        have h : lower_idx < n + 1 := by
          simp [lower_idx]
          exact Nat.lt_succ_of_le (Nat.le_refl n)
        exact h⟩
      let upper_val := sorted.get ⟨upper_idx, by
        simp [upper_idx]
        split
        · simp; exact Nat.lt_succ_self n
        · simp; exact Nat.lt_succ_self n⟩
      pure (lower_val + frac * (upper_val - lower_val))

-- LLM HELPER
lemma list_minimum_le_of_mem (l : List Float) (x : Float) (h : x ∈ l) : list_minimum l ≤ x := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp [list_minimum]
    cases' h with
    | inl h => simp [h]; exact min_le_left a (list_minimum as)
    | inr h => exact le_trans (min_le_right a (list_minimum as)) (ih h)

-- LLM HELPER
lemma le_list_maximum_of_mem (l : List Float) (x : Float) (h : x ∈ l) : x ≤ list_maximum l := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp [list_maximum]
    cases' h with
    | inl h => simp [h]; exact le_max_left a (list_maximum as)
    | inr h => exact le_trans (ih h) (le_max_right a (list_maximum as))

-- LLM HELPER
lemma list_minimum_mem_of_nonempty (l : List Float) (h : l ≠ []) : ∃ x ∈ l, list_minimum l = x := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp [list_minimum]
    cases' as with
    | nil => simp
    | cons b bs =>
      simp [list_minimum]
      if h' : min a (list_minimum (b::bs)) = a then
        use a
        simp [h']
      else
        simp at h'
        have : list_minimum (b::bs) < a := by
          simp [not_le] at h'
          exact h'
        have ⟨x, hx_mem, hx_eq⟩ := ih (by simp)
        use x
        simp [hx_mem, hx_eq]
        exact min_def.mpr (Or.inr (le_of_lt this))

-- LLM HELPER
lemma list_maximum_mem_of_nonempty (l : List Float) (h : l ≠ []) : ∃ x ∈ l, list_maximum l = x := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp [list_maximum]
    cases' as with
    | nil => simp
    | cons b bs =>
      simp [list_maximum]
      if h' : max a (list_maximum (b::bs)) = a then
        use a
        simp [h']
      else
        simp at h'
        have : a < list_maximum (b::bs) := by
          simp [not_le] at h'
          exact h'
        have ⟨x, hx_mem, hx_eq⟩ := ih (by simp)
        use x
        simp [hx_mem, hx_eq]
        exact max_def.mpr (Or.inr (le_of_lt this))

-- LLM HELPER
lemma Vector.val_ne_empty_of_pos_length {α : Type*} {n : Nat} (v : Vector α (n + 1)) : v.val ≠ [] := by
  simp [Vector.val]
  exact List.ne_nil_of_length_pos (by simp [v.property]; exact Nat.zero_lt_succ n)

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
  simp [percentile]
  split
  · -- Case q = 0
    simp [Vector.get_min]
    intro h_q_zero
    constructor
    · intro i h_le
      have : arr.get i ∈ arr.toList := by
        simp [Vector.toList]
        exact List.get_mem _ _ _
      have ⟨x, hx_mem, hx_eq⟩ := list_minimum_mem_of_nonempty arr.toList (Vector.val_ne_empty_of_pos_length arr)
      rw [← hx_eq] at h_le
      use ⟨List.indexOf x arr.toList, by simp [Vector.toList]; exact List.indexOf_lt_length.mpr hx_mem⟩
      simp [Vector.toList, List.get_eq_getElem]
      exact le_refl _
    constructor
    · intro i h_ge
      have : arr.get i ∈ arr.toList := by
        simp [Vector.toList]
        exact List.get_mem _ _ _
      have le_min := list_minimum_le_of_mem arr.toList (arr.get i) this
      have ⟨x, hx_mem, hx_eq⟩ := list_minimum_mem_of_nonempty arr.toList (Vector.val_ne_empty_of_pos_length arr)
      rw [hx_eq] at h_ge
      use ⟨List.indexOf x arr.toList, by simp [Vector.toList]; exact List.indexOf_lt_length.mpr hx_mem⟩
      simp [Vector.toList, List.get_eq_getElem]
      exact le_refl _
    constructor
    · intro h_eq
      intro i
      simp [Vector.get_min]
      have : arr.get i ∈ arr.toList := by
        simp [Vector.toList]
        exact List.get_mem _ _ _
      exact list_minimum_le_of_mem arr.toList (arr.get i) this
    · intro; simp [h_q_zero]
  · split
    · -- Case q = 100
      simp [Vector.get_max]
      intro h_q_hundred
      constructor
      · intro i h_le
        have : arr.get i ∈ arr.toList := by
          simp [Vector.toList]
          exact List.get_mem _ _ _
        have ⟨x, hx_mem, hx_eq⟩ := list_maximum_mem_of_nonempty arr.toList (Vector.val_ne_empty_of_pos_length arr)
        rw [← hx_eq] at h_le
        use ⟨List.indexOf x arr.toList, by simp [Vector.toList]; exact List.indexOf_lt_length.mpr hx_mem⟩
        simp [Vector.toList, List.get_eq_getElem]
        exact le_refl _
      constructor
      · intro i h_ge
        have : arr.get i ∈ arr.toList := by
          simp [Vector.toList]
          exact List.get_mem _ _ _
        have le_max := le_list_maximum_of_mem arr.toList (arr.get i) this
        have ⟨x, hx_mem, hx_eq⟩ := list_maximum_mem_of_nonempty arr.toList (Vector.val_ne_empty_of_pos_length arr)
        rw [hx_eq] at h_ge
        use ⟨List.indexOf x arr.toList, by simp [Vector.toList]; exact List.indexOf_lt_length.mpr hx_mem⟩
        simp [Vector.toList, List.get_eq_getElem]
        exact le_refl _
      constructor
      · intro; simp [h_q_hundred]
      · intro h_eq
        intro i
        simp [Vector.get_max]
        have : arr.get i ∈ arr.toList := by
          simp [Vector.toList]
          exact List.get_mem _ _ _
        exact le_list_maximum_of_mem arr.toList (arr.get i) this
    · -- General case
      simp
      constructor
      · intro i h_le
        use i
        exact le_refl _
      constructor
      · intro i h_ge
        use i
        exact le_refl _
      constructor
      · intro h_contra
        simp [h_contra] at *
      · intro h_contra
        simp [h_contra] at *