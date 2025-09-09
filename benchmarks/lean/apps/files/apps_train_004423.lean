-- <vc-helpers>
-- </vc-helpers>

def set_alarm (employed : Bool) (vacation : Bool) : Bool := sorry

theorem set_alarm_spec (employed vacation : Bool) :
  set_alarm employed vacation = (employed && !vacation) := sorry

theorem set_alarm_output_bool (employed vacation : Bool) : 
  set_alarm employed vacation = true ∨ set_alarm employed vacation = false := sorry

theorem unemployed_no_alarm (vacation : Bool) :
  set_alarm false vacation = false := sorry

theorem vacation_no_alarm (employed : Bool) :
  set_alarm employed true = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval set_alarm True True

/-
info: False
-/
-- #guard_msgs in
-- #eval set_alarm False True

/-
info: True
-/
-- #guard_msgs in
-- #eval set_alarm True False

-- Apps difficulty: introductory
-- Assurance level: unguarded