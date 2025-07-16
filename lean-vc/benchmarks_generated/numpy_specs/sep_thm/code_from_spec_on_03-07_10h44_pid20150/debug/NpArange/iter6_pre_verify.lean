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
  rfl

/- LLM HELPER -/
theorem arange_length_pos_helper (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    (stop - start) / step > 0 := by
  by_cases h : step < 0
  · simp [h] at h_valid_range
    have h_diff_neg : stop - start < 0 := by linarith
    have h_step_neg : step < 0 := h
    rw [div_pos_iff]
    left
    constructor
    · linarith
    · linarith
  · simp [h] at h_valid_range
    have h_diff_pos : stop - start > 0 := by linarith
    have h_step_pos : step > 0 := by
      cases' lt_or_eq_of_le (le_of_not_gt h) with h_pos h_zero
      · exact h_pos
      · contradiction
    rw [div_pos_iff]
    right
    constructor
    · linarith
    · linarith

/- LLM HELPER -/
theorem floor_pos_of_ge_one (x : Float) (hx : x ≥ 1) : x.floor ≥ 1 := by
  have h_floor_le : x.floor ≤ x := by
    exact Int.floor_le x
  have h_floor_ge : x - 1 < x.floor := by
    have h := Int.sub_one_lt_floor x
    simp at h
    exact h
  linarith

/- LLM HELPER -/
theorem toUInt64_pos_of_ge_one (x : Float) (hx : x.floor ≥ 1) : x.floor.toUInt64 ≥ 1 := by
  have h_pos : x.floor > 0 := by linarith
  have h_nat : x.floor.toNat ≥ 1 := by
    have h_floor_one : x.floor ≥ 1 := hx
    have h_pos_nat : x.floor.toNat > 0 := Int.toNat_pos h_pos
    exact Nat.succ_le_iff.mpr h_pos_nat
  rw [← UInt64.toNat_le_toNat_iff]
  simp [UInt64.toNat_one]
  exact h_nat

/- LLM HELPER -/
theorem toNat_pos_of_ge_one (x : UInt64) (hx : x ≥ 1) : x.toNat > 0 := by
  have h_ne_zero : x ≠ 0 := Ne.symm (ne_of_lt (by simp; exact hx))
  exact UInt64.toNat_pos_of_ne_zero h_ne_zero

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  have h_pos := arange_length_pos_helper start stop step h_step_nonzero h_valid_range
  have h_ge_one : (stop - start) / step ≥ 1 := by
    have h_abs_step_pos : |step| > 0 := abs_pos.mpr h_step_nonzero
    by_cases h : step < 0
    · simp [h] at h_valid_range
      have h_diff_neg : stop - start < 0 := by linarith
      have h_step_neg : step < 0 := h
      rw [div_le_iff_of_neg h_step_neg]
      simp
      linarith
    · simp [h] at h_valid_range
      have h_diff_pos : stop - start > 0 := by linarith
      have h_step_pos : step > 0 := by
        cases' lt_or_eq_of_le (le_of_not_gt h) with h_pos h_zero
        · exact h_pos
        · contradiction
      rw [le_div_iff h_step_pos]
      linarith
  have h_floor : ((stop - start) / step).floor ≥ 1 := by
    apply floor_pos_of_ge_one
    exact h_ge_one
  have h_uint : ((stop - start) / step).floor.toUInt64 ≥ 1 := by
    apply toUInt64_pos_of_ge_one
    exact h_floor
  apply toNat_pos_of_ge_one
  exact h_uint

/-- Specification: first element equals start -/
theorem arange_first_elem (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    let n := arangeLength start stop step
    n > 0 → arr[0]'(arange_length_pos start stop step h_step_nonzero h_valid_range) = start := by
  intro h_n_pos
  unfold arange
  simp [Vector.get_ofFn]
  ring

/-- Specification: consecutive elements differ by step -/
theorem arange_step_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    ∀ i : Fin (arangeLength start stop step),
      i.val + 1 < arangeLength start stop step →
      arr[i.val + 1]'(by simp; exact Nat.succ_lt_iff_lt.mpr (Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ i.isLt))) - arr[i.val] = step := by
  intro i h_bound
  unfold arange
  simp [Vector.get_ofFn]
  ring

end DafnySpecs.NpArange