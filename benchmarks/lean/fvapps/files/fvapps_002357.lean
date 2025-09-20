-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_student_record (s : String) : Bool := sorry

theorem empty_string_valid : 
  check_student_record "" = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem only_valid_chars_used (s : String) :
  s.data.all (fun c => c = 'P' ∨ c = 'L' ∨ c = 'A') → 
  ∃ (b : Bool), check_student_record s = b := sorry

theorem two_absences_fail (s : String) :
  (s.data.filter (· = 'A')).length ≥ 2 →
  check_student_record s = false := sorry

theorem three_consecutive_lates_fail (s : String) :
  s.data = [] ++ ['L', 'L', 'L'] ++ (List.drop 3 s.data) →
  check_student_record s = false := sorry

theorem all_present_pass (s : String) :
  s.length > 0 →
  (∀ c ∈ s.data, c = 'P') →
  check_student_record s = true := sorry

theorem no_absences_rule (s : String) :
  (∀ c ∈ s.data, c = 'P' ∨ c = 'L') →
  (¬(s.data = [] ++ ['L', 'L', 'L'] ++ (List.drop 3 s.data))) ↔
  check_student_record s = true := sorry
-- </vc-theorems>