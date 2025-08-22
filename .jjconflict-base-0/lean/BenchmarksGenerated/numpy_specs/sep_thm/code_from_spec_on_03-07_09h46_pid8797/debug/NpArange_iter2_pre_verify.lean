/-!
# Arange Array Creation Specification

Port of `np_arange.dfy` to Lean 4 using Vector types.

This module specifies the creation of arrays with evenly spaced values.
-/

namespace DafnySpecs.NpArange

/-- Calculate the length of an arange array given start, stop, and step -/
def arangeLength (start stop step : Float) : Nat := 
  ((stop - start) / step).floor.toUInt64.toNat

/-- Create an array of evenly spaced values within a given interval.

    Returns evenly spaced values from start (inclusive) to stop (exclusive),
    with the given step size.
-/
def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  Vector.ofFn (fun i => start + step * i.val.toFloat)

/-- Specification: the length matches the formula -/
theorem arange_length_correct (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step = ((stop - start) / step).floor.toUInt64.toNat := 
  by rfl

/- LLM HELPER -/
lemma arange_length_pos_aux (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    (stop - start) / step > 0 := by
  by_cases h : step < 0
  · simp [h] at h_valid_range
    have step_neg : step < 0 := h
    have start_gt_stop : start > stop := h_valid_range
    have num_pos : stop - start < 0 := by linarith
    exact div_pos_of_neg_of_neg num_pos step_neg
  · simp [h] at h_valid_range
    have step_pos : step > 0 := by
      cases' lt_or_gt_of_ne h_step_nonzero with h1 h2
      · contradiction
      · exact h2
    have start_lt_stop : start < stop := h_valid_range
    have num_pos : stop - start > 0 := by linarith
    exact div_pos num_pos step_pos

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  have h_pos := arange_length_pos_aux start stop step h_step_nonzero h_valid_range
  have h_floor_pos : ((stop - start) / step).floor > 0 := by
    apply Float.floor_pos
    exact h_pos
  have h_uint_pos : h_floor_pos.toUInt64.toNat > 0 := by
    apply Nat.pos_of_ne_zero
    intro h_eq
    have h_floor_nonneg : ((stop - start) / step).floor ≥ 0 := by
      apply Float.floor_nonneg
      linarith [h_pos]
    rw [Float.toUInt64_toNat_eq_zero_iff] at h_eq
    cases h_eq with
    | inl h => linarith [h_floor_pos]
    | inr h => linarith [h_floor_pos]
  exact h_uint_pos

/-- Specification: first element equals start -/
theorem arange_first_elem (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    let n := arangeLength start stop step
    n > 0 → arr[0]'(by simp; apply arange_length_pos; exact h_step_nonzero; exact h_valid_range) = start := by
  intro h_pos
  simp [arange, Vector.get_ofFn]
  simp [Nat.cast_zero, mul_zero, add_zero]

/-- Specification: consecutive elements differ by step -/
theorem arange_step_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    ∀ i : Fin (arangeLength start stop step),
      i.val + 1 < arangeLength start stop step →
      arr[i.val + 1]'(Nat.lt_of_succ_lt (Nat.succ_lt_succ i.isLt)) - arr[i.val] = step := by
  intro i h_bound
  simp [arange, Vector.get_ofFn]
  ring_nf
  rw [Nat.cast_add, Nat.cast_one]
  ring

end DafnySpecs.NpArange