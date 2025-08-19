/-!
# Arange Array Creation Specification

Port of `np_arange.dfy` to Lean 4 using Vector types.

This module specifies the creation of arrays with evenly spaced values.
-/

namespace DafnySpecs.NpArange

/-- Calculate the length of an arange array given start, stop, and step -/
def arangeLength (start stop step : Float) : Nat := 
  ((stop - start) / step).floor.toUInt64.toNat

/-- LLM HELPER -/
def arangeElem (start step : Float) (i : Nat) : Float :=
  start + step * Float.ofNat i

/-- Create an array of evenly spaced values within a given interval.

    Returns evenly spaced values from start (inclusive) to stop (exclusive),
    with the given step size.
-/
def arange (start stop step : Float)
    (_ : step ≠ 0)
    (_ : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  let n := arangeLength start stop step
  Vector.ofFn (fun i : Fin n => arangeElem start step i.val)

/-- Specification: the length matches the formula -/
theorem arange_length_correct (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step = ((stop - start) / step).floor.toUInt64.toNat := by
  rfl

/-- LLM HELPER -/
lemma step_sign_implies_pos_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    (stop - start) / step > 0 := by
  by_cases h : step < 0
  · simp [h] at h_valid_range
    have h_pos_diff : start - stop > 0 := by linarith
    have h_neg_step : step < 0 := h
    have : (stop - start) = -(start - stop) := by ring
    rw [this]
    have : -(start - stop) / step = (start - stop) / (-step) := by
      field_simp
      ring
    rw [this]
    apply div_pos h_pos_diff
    linarith
  · simp [h] at h_valid_range
    have h_pos_step : step > 0 := by
      cases' lt_or_gt_of_ne h_step_nonzero with h_neg h_pos
      · contradiction
      · exact h_pos
    apply div_pos
    · linarith
    · exact h_pos_step

/-- LLM HELPER -/
lemma Float.floor_pos (x : Float) (h : x > 0) : x.floor ≥ 0 := by
  simp [Float.floor]
  exact Int.floor_nonneg_of_nonneg (le_of_lt h)

/-- LLM HELPER -/
lemma Float.toUInt64_nonneg (x : Float) : x.toUInt64.toNat ≥ 0 := by
  exact Nat.zero_le _

/-- LLM HELPER -/
lemma arange_length_zero_contra (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop)
    (h_eq : ((stop - start) / step).floor.toUInt64.toNat = 0) : False := by
  have h_pos := step_sign_implies_pos_diff start stop step h_step_nonzero h_valid_range
  have h_floor_nonneg := Float.floor_pos ((stop - start) / step) h_pos
  simp [Float.toUInt64, UInt64.toNat] at h_eq
  have : ((stop - start) / step).floor ≥ 1 := by
    rw [Int.one_le_iff_zero_lt]
    exact Int.floor_pos.mpr (le_of_lt h_pos)
  simp [Float.toUInt64, UInt64.toNat, Float.toNat] at h_eq
  have : ((stop - start) / step).floor.toNat > 0 := by
    apply Int.toNat_pos
    exact this
  rw [h_eq] at this
  exact lt_irrefl 0 this

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp only [Nat.pos_iff_ne_zero]
  intro h_eq
  exact arange_length_zero_contra start stop step h_step_nonzero h_valid_range h_eq

/-- Specification: first element equals start -/
theorem arange_first_elem (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    let n := arangeLength start stop step
    n > 0 → arr[0]'(arange_length_pos start stop step h_step_nonzero h_valid_range) = start := by
  intro h_n_pos
  unfold arange
  simp only [Vector.getElem_ofFn]
  unfold arangeElem
  simp only [Float.ofNat]
  ring

/-- Specification: consecutive elements differ by step -/
theorem arange_step_diff (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    let arr := arange start stop step h_step_nonzero h_valid_range
    ∀ i : Fin (arangeLength start stop step),
      i.val + 1 < arangeLength start stop step →
      arr[i.val + 1]'(Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ (Fin.is_lt i))) - arr[i.val] = step := by
  intro i h_bound
  unfold arange
  simp only [Vector.getElem_ofFn]
  unfold arangeElem
  have : Float.ofNat (i.val + 1) = Float.ofNat i.val + Float.ofNat 1 := by
    rw [Float.ofNat_add]
  rw [this]
  ring_nf
  simp only [Float.ofNat]
  ring

end DafnySpecs.NpArange