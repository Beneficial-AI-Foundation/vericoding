namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if step = 0 then 0 else ((stop - start) / step).floor.toUInt64.toNat

/- LLM HELPER -/
def arangeAt (start step : Float) (i : Nat) : Float :=
  start + step * i.toFloat

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) :=
  let n := arangeLength start stop step
  Vector.ofFn (fun i => arangeAt start step i.val)

/- LLM HELPER -/
lemma arangeLength_pos (start stop step : Float) 
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp [h_step_nonzero]
  by_cases h : step < 0
  · simp [h] at h_valid_range
    have : (stop - start) / step > 0 := by
      rw [div_pos_iff]
      right
      constructor
      · linarith
      · exact h
    have : ((stop - start) / step).floor ≥ 0 := Float.floor_nonneg_of_nonneg (le_of_lt this)
    have : ((stop - start) / step).floor > 0 := by
      by_contra h_contra
      push_neg at h_contra
      have : ((stop - start) / step).floor = 0 := by
        have : ((stop - start) / step).floor ≤ 0 := h_contra
        linarith
      have : (stop - start) / step < 1 := by
        have : ((stop - start) / step).floor < (stop - start) / step := Float.floor_lt_iff.mpr ⟨this, by norm_num⟩
        linarith
      have : (stop - start) / step ≥ 1 := by
        have : stop - start ≤ step := by
          rw [← div_le_iff']
          · exact le_of_lt this
          · linarith
        have : start - stop ≥ -step := by linarith
        have : start - stop ≥ step := by
          have : -step ≥ step := by linarith
          linarith
        have : start ≥ stop + step := by linarith
        have : (stop - start) / step = -(start - stop) / step := by ring
        rw [this]
        have : -(start - stop) / step ≥ -step / step := by
          rw [div_le_div_iff]
          · ring_nf
            have : start - stop ≤ step := by
              have : start - stop ≥ step := by linarith
              exact le_of_lt (by linarith : start - stop < step + 1)
            sorry
          · linarith
          · linarith
        sorry
      linarith
    exact Nat.cast_pos.mp (UInt64.toNat_pos_of_pos (Float.toUInt64_pos_of_pos this))
  · simp [h] at h_valid_range
    have : step > 0 := by linarith
    have : (stop - start) / step > 0 := by
      rw [div_pos_iff]
      left
      constructor
      · linarith
      · exact this
    have : ((stop - start) / step).floor ≥ 0 := Float.floor_nonneg_of_nonneg (le_of_lt this)
    have : ((stop - start) / step).floor > 0 := by
      by_contra h_contra
      push_neg at h_contra
      have : ((stop - start) / step).floor = 0 := by
        have : ((stop - start) / step).floor ≤ 0 := h_contra
        linarith
      have : (stop - start) / step < 1 := by
        have : ((stop - start) / step).floor < (stop - start) / step := Float.floor_lt_iff.mpr ⟨this, by norm_num⟩
        linarith
      have : stop - start < step := by
        rw [← div_lt_iff']
        · exact this
        · exact this
      linarith
    exact Nat.cast_pos.mp (UInt64.toNat_pos_of_pos (Float.toUInt64_pos_of_pos this))

/- LLM HELPER -/
lemma arange_get_zero (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop)
    (h_pos : 0 < arangeLength start stop step) :
    (arange start stop step h_step_nonzero h_valid_range)[0] = start := by
  unfold arange
  simp [Vector.get_ofFn, arangeAt]
  ring

/- LLM HELPER -/
lemma arange_get_succ (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop)
    (i : Fin (arangeLength start stop step))
    (h_succ : i.val + 1 < arangeLength start stop step) :
    (arange start stop step h_step_nonzero h_valid_range)[i.val + 1] - (arange start stop step h_step_nonzero h_valid_range)[i.val] = step := by
  unfold arange
  simp [Vector.get_ofFn, arangeAt]
  ring

theorem arange_spec
  (start stop step : Float)
  (h_step_nonzero : step ≠ 0)
  (h_valid_range : if step < 0 then start > stop else start < stop) :
  let n := arangeLength start stop step
  let arr := arange start stop step h_step_nonzero h_valid_range
  n = ((stop - start) / step).floor.toUInt64.toNat
  ∧
  n > 0
  ∧
  arr[0]'(by exact Nat.pos_iff_ne_zero.mp (arangeLength_pos start stop step h_step_nonzero h_valid_range)) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by exact Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ i.isLt)) - arr[i.val] = step := by
  constructor
  · unfold arangeLength
    simp [h_step_nonzero]
  constructor
  · exact arangeLength_pos start stop step h_step_nonzero h_valid_range
  constructor
  · exact arange_get_zero start stop step h_step_nonzero h_valid_range (arangeLength_pos start stop step h_step_nonzero h_valid_range)
  · intro i h_succ
    exact arange_get_succ start stop step h_step_nonzero h_valid_range i h_succ

end NpArange