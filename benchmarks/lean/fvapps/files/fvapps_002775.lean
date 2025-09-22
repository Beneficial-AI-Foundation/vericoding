-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_availability (schedule : List (String × String)) (time : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_schedule_always_available
  (h : Nat) (m : Nat)
  (h_valid : h ≤ 23) (m_valid : m ≤ 59)
  (time := s!"{h}:{m}") :
  check_availability [] time = true := by
  sorry
-- </vc-theorems>