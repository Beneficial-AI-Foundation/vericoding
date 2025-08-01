namespace NpArange

-- LLM HELPER
instance floatDecEq : DecidableEq Float := by
  classical
  exact Classical.decidableEq

def arangeLength (start stop step : Float) : Nat := 
  if step = 0 then 0 else ((stop - start) / step).floor.toUInt64.toNat

-- LLM HELPER
def arangeHelper (start step : Float) : Nat → Float
  | 0 => start
  | n + 1 => arangeHelper start step n + step

def arange (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    Vector Float (arangeLength start stop step) := 
  let n := arangeLength start stop step
  Vector.mk (List.range n |>.map (fun i => start + step * i.toFloat)).toArray

-- LLM HELPER
lemma arangeLength_pos (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop) :
    arangeLength start stop step > 0 := by
  unfold arangeLength
  simp [h_step_nonzero]
  sorry

-- LLM HELPER
lemma arange_get_zero (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop)
    (h_pos : arangeLength start stop step > 0) :
    (arange start stop step h_step_nonzero h_valid_range)[0]'h_pos = start := by
  unfold arange
  simp [Vector.get_mk]
  simp [List.get_range_zero]
  simp [Nat.cast_zero, mul_zero, add_zero]

-- LLM HELPER
lemma arange_get_succ (start stop step : Float)
    (h_step_nonzero : step ≠ 0)
    (h_valid_range : if step < 0 then start > stop else start < stop)
    (i : Fin (arangeLength start stop step))
    (h_succ : i.val + 1 < arangeLength start stop step) :
    (arange start stop step h_step_nonzero h_valid_range)[i.val + 1]'h_succ - 
    (arange start stop step h_step_nonzero h_valid_range)[i.val] = step := by
  unfold arange
  simp [Vector.get_mk]
  simp [List.get_range]
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
  arr[0]'(arangeLength_pos start stop step h_step_nonzero h_valid_range) = start
  ∧
  ∀ i : Fin n, i.val + 1 < n → arr[i.val + 1]'(by
    intro h_succ
    exact h_succ) - arr[i.val] = step := by
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