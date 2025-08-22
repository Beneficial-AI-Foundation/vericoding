namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if h : step = 0 then 0
  else if step < 0 then
    if start > stop then ((stop - start) / step).floor.toUInt64.toNat else 0
  else
    if start < stop then ((stop - start) / step).floor.toUInt64.toNat else 0

/- LLM HELPER -/
def arangeHelper (start step : Float) (n : Nat) : List Float :=
  match n with
  | 0 => []
  | Nat.succ m => start :: arangeHelper (start + step) step m

/- LLM HELPER -/
lemma arangeHelper_length (start step : Float) (n : Nat) : 
  (arangeHelper start step n).length = n := by
  induction n with
  | zero => simp [arangeHelper]
  | succ n ih => simp [arangeHelper, ih]

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := by
  let n := arangeLength start stop step
  let list := arangeHelper start step n
  have h_len : list.length = n := arangeHelper_length start step n
  exact ⟨list.toArray, by simp [h_len]⟩

/- LLM HELPER -/
lemma arangeLength_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp [h_step_nonzero]
  by_cases h : step < 0
  · simp [h]
    have : start > stop := by
      rw [if_pos h] at h_valid_range
      exact h_valid_range
    have : (stop - start) / step > 0 := by
      have : stop - start < 0 := by linarith
      exact div_pos_of_neg_of_neg this h
    have : ((stop - start) / step).floor.toUInt64.toNat > 0 := by
      have : (stop - start) / step ≥ 1 := by
        have : -1 ≤ (stop - start) / step := by
          rw [div_le_iff']
          · linarith
          · linarith
        linarith
      have : ((stop - start) / step).floor ≥ 1 := by
        apply Float.floor_le_of_le
        exact this
      have : ((stop - start) / step).floor.toUInt64 ≥ 1 := by
        simp [Float.toUInt64]
        exact this
      exact Nat.cast_pos.mp (by simp; exact this)
    exact this
  · simp [h]
    have : start < stop := by
      rw [if_neg h] at h_valid_range
      exact h_valid_range
    have step_pos : step > 0 := by
      by_contra h_not_pos
      push_neg at h_not_pos
      have : step ≤ 0 := h_not_pos
      cases' le_iff_eq_or_lt.mp this with h_eq h_lt
      · exact h_step_nonzero h_eq
      · exact h h_lt
    have : (stop - start) / step > 0 := by
      have : stop - start > 0 := by linarith
      exact div_pos this step_pos
    have : ((stop - start) / step).floor.toUInt64.toNat > 0 := by
      have : (stop - start) / step ≥ 1 := by
        rw [div_le_iff]
        · linarith
        · exact step_pos
      have : ((stop - start) / step).floor ≥ 1 := by
        apply Float.floor_le_of_le
        exact this
      have : ((stop - start) / step).floor.toUInt64 ≥ 1 := by
        simp [Float.toUInt64]
        exact this
      exact Nat.cast_pos.mp (by simp; exact this)
    exact this

/- LLM HELPER -/
lemma arangeHelper_first (start step : Float) (n : Nat) (h : n > 0) :
    (arangeHelper start step n).head? = some start := by
  cases n with
  | zero => contradiction
  | succ n => simp [arangeHelper]

/- LLM HELPER -/
lemma arangeHelper_get (start step : Float) (n : Nat) (i : Nat) (h : i < n) :
    (arangeHelper start step n)[i]? = some (start + i.cast * step) := by
  induction n, i using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases i with
      | zero => 
        simp [arangeHelper]
        simp [Nat.cast_zero]
        ring
      | succ i' =>
        simp [arangeHelper]
        have : i' < n' := by omega
        rw [ih n' (by omega) i' this]
        simp [Nat.cast_add, Nat.cast_one]
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
  arr[0]'(by
    have h_pos := arangeLength_pos start stop step h_step_nonzero h_valid_range
    omega) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by
    have h_pos := arangeLength_pos start stop step h_step_nonzero h_valid_range
    omega) - arr[i.val] = step := by
  constructor
  · -- n = ((stop - start) / step).floor.toUInt64.toNat
    unfold arangeLength
    simp [h_step_nonzero]
    by_cases h : step < 0
    · simp [h, h_valid_range]
    · simp [h, h_valid_range]
  constructor
  · -- n > 0
    exact arangeLength_pos start stop step h_step_nonzero h_valid_range
  constructor
  · -- arr[0] = start
    unfold arange
    simp [Vector.get]
    have h_pos := arangeLength_pos start stop step h_step_nonzero h_valid_range
    have h_get : (arangeHelper start step (arangeLength start stop step))[0]? = some start := by
      apply arangeHelper_get
      omega
    rw [List.get?_eq_some] at h_get
    obtain ⟨val, eq⟩ := h_get
    simp [eq]
    have : val = start := by
      have : val = start + (0 : Nat).cast * step := by
        rw [←eq]
        apply arangeHelper_get
        omega
      simp at this
      exact this
    exact this
  · -- step property
    intro i h_bound
    unfold arange
    simp [Vector.get]
    have h_get_i : (arangeHelper start step (arangeLength start stop step))[i.val]? = some (start + i.val.cast * step) := by
      apply arangeHelper_get
      exact i.isLt
    have h_get_i_plus_1 : (arangeHelper start step (arangeLength start stop step))[i.val + 1]? = some (start + (i.val + 1).cast * step) := by
      apply arangeHelper_get
      exact h_bound
    rw [List.get?_eq_some] at h_get_i h_get_i_plus_1
    obtain ⟨val_i, eq_i⟩ := h_get_i
    obtain ⟨val_i_plus_1, eq_i_plus_1⟩ := h_get_i_plus_1
    simp [eq_i, eq_i_plus_1]
    have : val_i = start + i.val.cast * step := by
      rw [←eq_i]
      apply arangeHelper_get
      exact i.isLt
    have : val_i_plus_1 = start + (i.val + 1).cast * step := by
      rw [←eq_i_plus_1]
      apply arangeHelper_get
      exact h_bound
    simp [this]
    ring

end NpArange