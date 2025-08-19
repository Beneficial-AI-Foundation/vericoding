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
    arangeLength start stop step = ((stop - start) / step).floor.toUInt64.toNat := 
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
lemma Float.floor_pos (x : Float) (h : x > 0) : x.floor > 0 := by
  simp [Float.floor]
  exact Int.floor_pos.mpr (le_of_lt h)

/-- LLM HELPER -/
lemma Float.toUInt64_pos_of_pos (x : Float) (h : x > 0) : x.toUInt64 > 0 := by
  simp [Float.toUInt64]
  have : x.toNat > 0 := by
    simp [Float.toNat]
    exact Nat.pos_of_ne_zero (ne_of_gt (Float.toNat_pos_of_pos h))
  exact this

/-- LLM HELPER -/
lemma Float.toNat_pos_of_pos (x : Float) (h : x > 0) : x.toNat ≠ 0 := by
  simp [Float.toNat]
  intro h_eq
  have : x ≥ 0 := le_of_lt h
  contradiction

/-- LLM HELPER -/
lemma UInt64.toNat_pos (x : UInt64) (h : x > 0) : x.toNat > 0 := by
  simp [UInt64.toNat]
  exact Nat.pos_of_ne_zero (ne_of_gt (UInt64.val_pos_of_pos h))

/-- LLM HELPER -/
lemma UInt64.val_pos_of_pos (x : UInt64) (h : x > 0) : x.val ≠ 0 := by
  intro h_eq
  rw [h_eq] at h
  simp at h

/-- Specification: the result has positive length -/
theorem arange_length_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp [Nat.pos_iff_ne_zero]
  intro h_eq
  have h_pos := step_sign_implies_pos_diff start stop step h_step_nonzero h_valid_range
  have : ((stop - start) / step).floor.toUInt64 = 0 := by
    rw [UInt64.ext_iff]
    simp [h_eq]
  exfalso
  have h_floor_pos := Float.floor_pos ((stop - start) / step) h_pos
  have : ((stop - start) / step).floor.toUInt64 > 0 := by
    apply Float.toUInt64_pos_of_pos
    exact h_floor_pos
  rw [this] at *
  simp at *

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
  unfold arangeElem
  simp [Float.ofNat]
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
  simp [Vector.get_ofFn]
  unfold arangeElem
  have : Float.ofNat (i.val + 1) = Float.ofNat i.val + Float.ofNat 1 := by
    rw [Float.ofNat_add]
  rw [this]
  ring_nf
  simp [Float.ofNat]
  ring

end DafnySpecs.NpArange