namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if step = 0 then 0
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
  exact ⟨list, h_len⟩

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
    sorry
  · simp [h]
    have : start < stop := by
      rw [if_neg h] at h_valid_range
      exact h_valid_range
    sorry

/- LLM HELPER -/
lemma arangeHelper_first (start step : Float) (n : Nat) (h : n > 0) :
    (arangeHelper start step n).head? = some start := by
  cases n with
  | zero => contradiction
  | succ n => simp [arangeHelper]

/- LLM HELPER -/
lemma arangeHelper_step (start step : Float) (n : Nat) (i : Nat) 
    (h1 : i < n) (h2 : i + 1 < n) :
    (arangeHelper start step n)[i + 1]? = some (start + (i + 1 : Nat).cast * step) := by
  sorry

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
    cases h_pos_cases : arangeLength start stop step with
    | zero => omega
    | succ m => simp [arangeHelper]
  · -- step property
    intro i h_bound
    unfold arange
    simp [Vector.get]
    sorry

end NpArange