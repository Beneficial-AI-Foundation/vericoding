-- <vc-helpers>
-- </vc-helpers>

def check_availability (schedule : List (String × String)) (time : String) : Bool :=
  sorry

theorem empty_schedule_always_available
  (h : Nat) (m : Nat)
  (h_valid : h ≤ 23) (m_valid : m ≤ 59)
  (time := s!"{h}:{m}") :
  check_availability [] time = true := by
  sorry

/-
info: '10:15'
-/
-- #guard_msgs in
-- #eval check_availability [["09:30", "10:15"], ["12:20", "15:50"]] "10:00"

/-
info: True
-/
-- #guard_msgs in
-- #eval check_availability [["09:30", "10:15"], ["12:20", "15:50"]] "11:00"

/-
info: True
-/
-- #guard_msgs in
-- #eval check_availability [] "10:15"

-- Apps difficulty: introductory
-- Assurance level: unguarded