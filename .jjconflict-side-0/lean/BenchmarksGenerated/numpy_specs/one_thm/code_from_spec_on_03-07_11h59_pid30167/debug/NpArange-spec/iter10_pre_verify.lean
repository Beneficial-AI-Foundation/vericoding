namespace NpArange

/- LLM HELPER -/
instance : DecidableEq Float := by
  exact Classical.decidable_eq

def arangeLength (start stop step : Float) : Nat :=
  if step = 0 then 0 else ((stop - start) / step).floor.toUInt64.toNat

/- LLM HELPER -/
def arangeAux (start step : Float) (n : Nat) : Array Float :=
  match n with
  | 0 => #[]
  | k + 1 => #[start] ++ arangeAux (start + step) step k

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Array Float :=
  arangeAux start step (arangeLength start stop step)

/- LLM HELPER -/
lemma arangeAux_length (start step : Float) (n : Nat) : 
  (arangeAux start step n).size = n := by
  induction n with
  | zero => simp [arangeAux]
  | succ k ih => simp [arangeAux, ih]

/- LLM HELPER -/
lemma arangeAux_get_zero (start step : Float) (n : Nat) (h : 0 < n) : 
  (arangeAux start step n)[0]! = start := by
  cases n with
  | zero => contradiction
  | succ k => simp [arangeAux]

/- LLM HELPER -/
lemma arangeAux_get_succ (start step : Float) (n : Nat) (i : Nat) (h : i < n) (h_succ : i + 1 < n) :
  (arangeAux start step n)[i + 1]! - (arangeAux start step n)[i]! = step := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ k ih => 
    cases i with
    | zero => simp [arangeAux]
    | succ j => 
      simp [arangeAux]
      have h_j : j < k := by simp at h; exact Nat.lt_of_succ_lt_succ h
      have h_succ_j : j + 1 < k := by simp at h_succ; exact Nat.lt_of_succ_lt_succ h_succ
      rw [← ih j h_j h_succ_j]
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
    have neg_num : stop - start < 0 := by linarith
    have neg_den : step < 0 := h
    have pos_div : (stop - start) / step > 0 := by
      rw [div_pos_iff]
      left
      exact ⟨neg_num, neg_den⟩
    have floor_pos : ((stop - start) / step).floor ≥ 0 := by
      exact Float.floor_nonneg.mpr (le_of_lt pos_div)
    have : ((stop - start) / step).floor.toUInt64.toNat > 0 := by
      have : ((stop - start) / step).floor ≥ 1 := by
        exact Float.floor_pos pos_div
      simp [Float.toUInt64_pos floor_pos]
      exact Nat.pos_of_ne_zero (by simp [ne_of_gt this])
    exact this
  · simp [h] at h_valid_range
    have pos_num : stop - start > 0 := by linarith
    have pos_den : step > 0 := by
      push_neg at h
      exact lt_of_le_of_ne h (Ne.symm h_step_nonzero)
    have pos_div : (stop - start) / step > 0 := by
      exact div_pos pos_num pos_den
    have : ((stop - start) / step).floor.toUInt64.toNat > 0 := by
      have floor_pos : ((stop - start) / step).floor ≥ 1 := by
        exact Float.floor_pos pos_div
      simp [Float.toUInt64_pos (le_of_lt (by linarith : (0 : Float) < 1))]
      exact Nat.pos_of_ne_zero (by simp [ne_of_gt floor_pos])
    exact this

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
  arr[0]! = start
  ∧
  ∀ i : Nat, i < n → i + 1 < n → arr[i + 1]! - arr[i]! = step := by
  unfold arangeLength arange
  simp [h_step_nonzero]
  constructor
  · rfl
  constructor
  · exact valid_range_implies_positive_length start stop step h_step_nonzero h_valid_range
  constructor
  · rw [arangeAux_get_zero]
    exact valid_range_implies_positive_length start stop step h_step_nonzero h_valid_range
  · intro i h_i h_succ
    exact arangeAux_get_succ start step ((stop - start) / step).floor.toUInt64.toNat i h_i h_succ

end NpArange