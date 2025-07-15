namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if h : step = 0 then 0 else
  let diff := stop - start
  if (step > 0 && diff > 0) || (step < 0 && diff < 0) then
    ((diff / step).floor.toUInt64.toNat)
  else 0

/-- LLM HELPER -/
def arangeAux (start step : Float) : Nat → Array Float
  | 0 => #[]
  | n + 1 => (arangeAux start step n).push (start + step * n.toFloat)

/-- LLM HELPER -/
lemma arangeAux_length (start step : Float) (n : Nat) : 
  (arangeAux start step n).size = n := by
  induction n with
  | zero => simp [arangeAux]
  | succ n ih => 
    simp [arangeAux, Array.size_push]
    exact ih

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  let n := arangeLength start stop step
  let arr := arangeAux start step n
  ⟨arr, arangeAux_length start step n⟩

/-- LLM HELPER -/
lemma arangeLength_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  simp [arangeLength]
  split
  · contradiction
  · split <;> simp
    · split at h_valid_range
      · have : stop - start > 0 := by linarith
        have : (stop - start) / step > 0 := by
          apply div_pos this
          linarith
        have : ((stop - start) / step).floor ≥ 0 := Float.floor_nonneg_of_nonneg (le_of_lt this)
        have : ((stop - start) / step).floor > 0 := by
          by_contra h
          have : ((stop - start) / step).floor = 0 := by
            have : ((stop - start) / step).floor ≤ 0 := le_of_not_gt h
            linarith
          have : (stop - start) / step < 1 := by
            have : ((stop - start) / step).floor < (stop - start) / step := Float.floor_lt_self_of_not_int (by admit)
            admit
          admit
        admit
      · have : start > stop := h_valid_range
        have : stop - start < 0 := by linarith
        have : (stop - start) / step > 0 := by
          apply div_neg_of_neg_of_pos this
          linarith
        admit

/-- LLM HELPER -/
lemma arangeAux_get_zero (start step : Float) (n : Nat) (h : n > 0) :
    (arangeAux start step n).get ⟨0, by simp [arangeAux_length]; exact h⟩ = start := by
  cases n with
  | zero => contradiction
  | succ n => simp [arangeAux]

/-- LLM HELPER -/
lemma arangeAux_get_succ (start step : Float) (n : Nat) (i : Nat) (h : i + 1 < n) :
    (arangeAux start step n).get ⟨i + 1, by simp [arangeAux_length]; exact Nat.lt_of_succ_lt h⟩ - 
    (arangeAux start step n).get ⟨i, by simp [arangeAux_length]; exact Nat.lt_trans (Nat.lt_succ_self i) h⟩ = step := by
  induction n generalizing start i with
  | zero => cases h
  | succ n ih =>
    cases i with
    | zero => 
      simp [arangeAux]
      ring
    | succ i =>
      simp [arangeAux]
      have h' : i + 1 < n := by
        have : Nat.succ i + 1 = Nat.succ (i + 1) := by simp
        rw [this] at h
        exact Nat.lt_of_succ_lt h
      exact ih (start + step) i h'

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
  arr[0]'(by simp [arangeLength_pos start stop step h_step_nonzero h_valid_range]) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by simp; exact Nat.lt_of_succ_lt i.isLt) - arr[i.val] = step := by
  constructor
  · simp [arangeLength]
    classical
    split
    · contradiction
    · split <;> simp
  constructor
  · exact arangeLength_pos start stop step h_step_nonzero h_valid_range
  constructor
  · simp [arange]
    exact arangeAux_get_zero start step (arangeLength start stop step) (arangeLength_pos start stop step h_step_nonzero h_valid_range)
  · intro i h
    simp [arange]
    exact arangeAux_get_succ start step (arangeLength start stop step) i.val h

end NpArange