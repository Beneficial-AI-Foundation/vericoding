-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validFormat (s : String) : Bool := sorry

def meetingTime (ta tb r : Float) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_period_format (ta : Float) (h : ta ≠ 0) :
  validFormat (meetingTime ta 0 5) := sorry

theorem zero_period_value_nonzero (ta : Float) (h : ta ≠ 0) :
  ∃ x : Float, Float.abs (x - Float.abs ta) < 0.01 ∧ 
  meetingTime ta 0 5 = toString x := sorry

theorem zero_period_value_zero :
  meetingTime 0 0 5 = "0.00" := sorry

theorem meeting_time_format (ta tb : Float) (r : Float) 
  (h1 : ta ≠ tb) (h2 : ta ≠ 0) (h3 : tb ≠ 0) (h4 : r ≥ 0.1) (h5 : r ≤ 1000) :
  validFormat (meetingTime ta tb r) := sorry

theorem meeting_time_positive (ta tb : Float) (r : Float)
  (h1 : ta ≠ tb) (h2 : ta ≠ 0) (h3 : tb ≠ 0) (h4 : r ≥ 0.1) (h5 : r ≤ 1000) :
  ∃ x : Float, x ≥ 0 ∧ meetingTime ta tb r = toString x := sorry

theorem meeting_time_scaling (ta tb : Float) (r : Float)
  (h1 : ta ≠ tb) (h2 : ta ≠ 0) (h3 : tb ≠ 0) (h4 : r ≥ 0.1) (h5 : r ≤ 1000) :
  ∃ x y : Float, 
    meetingTime ta tb r = toString x ∧ 
    meetingTime (2*ta) (2*tb) r = toString y ∧
    Float.abs (y - 2*x) < 0.1 := sorry
-- </vc-theorems>