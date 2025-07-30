namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if step = 0 then 0 else ((stop - start) / step).floor.toUInt64.toNat

/- LLM HELPER -/
def arangeAux (start step : Float) (n : Nat) : Vector Float n :=
  match n with
  | 0 => Vector.nil
  | k + 1 => Vector.cons start (arangeAux (start + step) step k)

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := by
  unfold arangeLength
  simp [h_step_nonzero]
  exact arangeAux start step ((stop - start) / step).floor.toUInt64.toNat

/- LLM HELPER -/
lemma arangeAux_length (start step : Float) (n : Nat) : 
  (arangeAux start step n).length = n := by
  induction n with
  | zero => simp [arangeAux]
  | succ k ih => simp [arangeAux, ih]

/- LLM HELPER -/
lemma arangeAux_get_zero (start step : Float) (n : Nat) (h : 0 < n) : 
  (arangeAux start step n).get ⟨0, h⟩ = start := by
  cases n with
  | zero => contradiction
  | succ k => simp [arangeAux, Vector.get]

/- LLM HELPER -/
lemma arangeAux_get_succ (start step : Float) (n : Nat) (i : Fin n) (h : i.val + 1 < n) :
  (arangeAux start step n).get ⟨i.val + 1, by simp; exact h⟩ - (arangeAux start step n).get i = step := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero _ i.isLt)
  | succ k => 
    cases i with
    | mk val isLt =>
      simp [arangeAux, Vector.get]
      cases val with
      | zero => simp [arangeAux, Vector.get]
      | succ j => 
        simp [Vector.get]
        have h_j : j < k := by simp at isLt; exact Nat.lt_of_succ_lt_succ isLt
        have h_succ : j + 1 < k := by simp at h; exact Nat.lt_of_succ_lt_succ h
        rw [← arangeAux_get_succ (start + step) step k ⟨j, h_j⟩ h_succ]
        ring

/- LLM HELPER -/
lemma valid_range_implies_positive_length (start stop step : Float)
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
      · linarith
    simp [Float.floor_pos this]
  · simp [h] at h_valid_range
    have : (stop - start) / step > 0 := by
      rw [div_pos_iff]
      left
      constructor
      · linarith
      · linarith [le_of_not_gt h]
    simp [Float.floor_pos this]

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
  arr[0]'(by exact valid_range_implies_positive_length start stop step h_step_nonzero h_valid_range) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by simp [n]; exact Nat.lt_of_succ_lt (i.val + 1) n (by assumption)) - arr[i.val] = step := by
  simp [arangeLength, arange]
  simp [h_step_nonzero]
  constructor
  · rfl
  constructor
  · exact valid_range_implies_positive_length start stop step h_step_nonzero h_valid_range
  constructor
  · rw [arangeAux_get_zero]
  · intro i h
    rw [arangeAux_get_succ]
    exact h

end NpArange