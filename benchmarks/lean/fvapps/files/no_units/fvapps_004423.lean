-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def set_alarm (employed : Bool) (vacation : Bool) : Bool := sorry

theorem set_alarm_spec (employed vacation : Bool) :
  set_alarm employed vacation = (employed && !vacation) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem set_alarm_output_bool (employed vacation : Bool) : 
  set_alarm employed vacation = true ∨ set_alarm employed vacation = false := sorry

theorem unemployed_no_alarm (vacation : Bool) :
  set_alarm false vacation = false := sorry

theorem vacation_no_alarm (employed : Bool) :
  set_alarm employed true = false := sorry
-- </vc-theorems>