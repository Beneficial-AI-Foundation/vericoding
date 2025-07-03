/-!
# Arange Array Creation Specification

Port of `np_arange.dfy` to Lean 4 using Vector types.

This module specifies the creation of arrays with evenly spaced values.
-/

namespace DafnySpecs.NpArange

/-- Calculate the length of an arange array given start, stop, and step -/
def arangeLength (start stop step : Float) : Nat := 
  max 0 ((stop - start) / step).floor.toUInt64.toNat

/-- Create an array of evenly spaced values within a given interval.

    Returns evenly spaced values from start (inclusive) to stop (exclusive),
    with the given step size.
-/
def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  Vector.ofFn (fun i => start + step * i.val.toFloat)

/- LLM HELPER -/
lemma max_eq_self_when_nonneg (a b : Nat) (h : a ≥ b) : max b a = a := by
  exact Nat.max_eq_right h

/- LLM HELPER -/
lemma arange_length_nonneg (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    ((stop - start) / step).floor.toUInt64.toNat ≥ 0 := by
  exact Nat.zero_le _

/-- Specification: the length matches the formula -/
theorem arange_length_correct (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step = ((stop - start) / step).floor.toUInt64.toNat := by
  unfold arangeLength
  rw [max_eq_self_when_nonneg]
  exact arange_length_nonneg start stop step h_step_nonzero h_valid_range

/- LLM HELPER -/
lemma arange_length_pos_helper (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    ((stop - start) / step).floor.toUInt64.toNat > 0 := by
  have h_pos : (stop - start) / step > 0 := by
    cases' h_valid_range with h_neg h_pos
    · simp at h_neg
      cases' h_neg with h_step_neg h_start_gt_stop
      have h_num_neg : stop - start < 0 := by linarith
      exact div_pos_of_neg_of_neg h_num_neg h_step_neg
    · simp at h_pos
      cases' h_pos with h_step_pos h_start_lt_stop
      have h_num_pos : stop - start > 0 := by linarith
      exact div_pos h_num_pos h_step_pos
  have h_floor_pos : ((stop - start) / step).floor > 0 := by
    exact Int.floor_pos.mpr h_pos
  exact Nat.pos_iff_ne_zero.mpr (fun h => by
    simp [Int.toUInt64_toNat_eq_zero_iff] at h
    cases' h with h_neg h_zero
    · linarith
    · linarith)

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  rw [Nat.lt_max_iff]
  right
  exact arange_length_pos_helper start stop step h_step_nonzero h_valid_range

/-- Specification: first element equals start -/
theorem arange_first_elem (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    let n := arangeLength start stop step
    n > 0 → arr[0]'(arange_length_pos start stop step h_step_nonzero h_valid_range) = start := by
  intro h_pos
  simp [arange, Vector.get_ofFn]
  ring

/-- Specification: consecutive elements differ by step -/
theorem arange_step_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    ∀ i : Fin (arangeLength start stop step),
      i.val + 1 < arangeLength start stop step →
      arr[i.val + 1]'(by simp [*]) - arr[i.val] = step := by
  intro i h_bound
  simp [arange, Vector.get_ofFn]
  ring

end DafnySpecs.NpArange