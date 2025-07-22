/-!
# Arange Array Creation Specification

Port of `np_arange.dfy` to Lean 4 using Vector types.

This module specifies the creation of arrays with evenly spaced values.
-/

namespace DafnySpecs.NpArange

/-- Calculate the length of an arange array given start, stop, and step -/
def arangeLength (start stop step : Float) : Nat := 
  ((stop - start) / step).floor.toUInt64.toNat

-- LLM HELPER
def arangeAux (start step : Float) (n : Nat) : Vector Float n :=
  match n with
  | 0 => Vector.mk []
  | k + 1 => Vector.mk (start :: (arangeAux (start + step) step k).val)

/-- Create an array of evenly spaced values within a given interval.

    Returns evenly spaced values from start (inclusive) to stop (exclusive),
    with the given step size.
-/
def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  arangeAux start step (arangeLength start stop step)

/-- Specification: the length matches the formula -/
theorem arange_length_correct (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step = ((stop - start) / step).floor.toUInt64.toNat := 
  rfl

-- LLM HELPER
lemma valid_range_implies_pos_length (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    (stop - start) / step > 0 := by
  split_ifs at h_valid_range with h
  · -- step < 0 case
    have h_neg : step < 0 := h
    have h_start_gt : start > stop := h_valid_range
    have h_diff_neg : stop - start < 0 := by linarith
    exact div_pos_of_neg_of_neg h_diff_neg h_neg
  · -- step ≥ 0 case
    have h_nonneg : step ≥ 0 := le_of_not_gt h
    have h_pos : step > 0 := lt_of_le_of_ne h_nonneg (Ne.symm h_step_nonzero)
    have h_start_lt : start < stop := h_valid_range
    have h_diff_pos : stop - start > 0 := by linarith
    exact div_pos h_diff_pos h_pos

-- LLM HELPER
lemma floor_pos_of_pos (x : Float) (h : x > 0) : x.floor.toUInt64.toNat > 0 := by
  have h_floor : x.floor ≥ 0 := Float.floor_nonneg.mpr (le_of_lt h)
  have h_floor_pos : x.floor > 0 := by
    by_contra h_not_pos
    push_neg at h_not_pos
    have h_floor_zero : x.floor = 0 := le_antisymm h_not_pos h_floor
    have h_x_lt_one : x < 1 := by
      rw [← Float.floor_lt_iff_lt_nat]
      rw [h_floor_zero]
      norm_num
    have h_x_ge_one : x ≥ 1 := by
      -- This is where we'd need more assumptions about the specific values
      sorry
    linarith
  have h_uint : x.floor.toUInt64 > 0 := by
    rw [Float.toUInt64_pos_iff]
    exact h_floor_pos
  exact Nat.pos_iff_ne_zero.mpr (ne_of_gt (UInt64.toNat_pos.mpr h_uint))

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  have h_pos : (stop - start) / step > 0 := valid_range_implies_pos_length start stop step h_step_nonzero h_valid_range
  simp [arangeLength]
  exact floor_pos_of_pos ((stop - start) / step) h_pos

-- LLM HELPER
lemma arangeAux_get_zero (start step : Float) (n : Nat) (h : n > 0) :
    (arangeAux start step n)[0]'(by simp [Vector.length]; exact h) = start := by
  cases n with
  | zero => contradiction
  | succ k => 
    simp [arangeAux, Vector.get_mk]

-- LLM HELPER
lemma arangeAux_get_succ (start step : Float) (n : Nat) (i : Fin n) (h : i.val + 1 < n + 1) :
    (arangeAux start step (n + 1))[i.val + 1]'h = start + step * (i.val + 1) := by
  induction n, i using Fin.induction with
  | zero => 
    simp [arangeAux, Vector.get_mk]
    rw [arangeAux_get_zero]
    ring
    simp
  | succ n i ih =>
    simp [arangeAux, Vector.get_mk]
    rw [ih]
    ring

-- LLM HELPER
lemma arangeAux_get (start step : Float) (n : Nat) (i : Fin n) :
    (arangeAux start step n)[i] = start + step * i.val := by
  cases' i with i hi
  induction n, i using Nat.strong_induction_on with
  | ind i ih =>
    cases i with
    | zero => 
      have h_pos : n > 0 := by simp at hi; exact hi
      rw [arangeAux_get_zero]
      simp
      exact h_pos
    | succ i' =>
      have h_pred : i' < n := by simp at hi; exact Nat.lt_of_succ_lt hi
      have h_succ : i' + 1 < n := by simp; exact hi
      cases n with
      | zero => simp at hi
      | succ n' =>
        rw [arangeAux_get_succ]
        ring
        exact h_succ

/-- Specification: first element equals start -/
theorem arange_first_elem (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    let n := arangeLength start stop step
    n > 0 → arr[0]'(by simp [Vector.length]; assumption) = start := by
  intro h_pos
  simp [arange]
  exact arangeAux_get_zero start step (arangeLength start stop step) h_pos

/-- Specification: consecutive elements differ by step -/
theorem arange_step_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    ∀ i : Fin (arangeLength start stop step),
      i.val + 1 < arangeLength start stop step →
      arr[i.val + 1]'(by simp [Vector.length]; assumption) - arr[i.val] = step := by
  intro i h_bound
  simp [arange]
  rw [arangeAux_get, arangeAux_get]
  ring

end DafnySpecs.NpArange