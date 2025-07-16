namespace NpArange

def arangeLength (start stop step : Float) : Nat :=
  if h : step = 0 then 0 else ((stop - start) / step).floor.toUInt64.toNat

/- LLM HELPER -/
def arangeAt (start step : Float) (i : Nat) : Float :=
  start + step * i.toFloat

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) :=
  let n := arangeLength start stop step
  Vector.ofFn fun i => arangeAt start step i.val

/- LLM HELPER -/
lemma arangeLength_pos (start stop step : Float) 
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp [h_step_nonzero]
  sorry

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
    (arange start stop step h_step_nonzero h_valid_range)[⟨i.val + 1, h_succ⟩] - (arange start stop step h_step_nonzero h_valid_range)[i] = step := by
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
  ∀ i : Fin n, i.val + 1 < n → arr[⟨i.val + 1, by assumption⟩] - arr[i] = step := by
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