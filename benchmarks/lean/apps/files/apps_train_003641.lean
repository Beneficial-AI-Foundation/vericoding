-- <vc-helpers>
-- </vc-helpers>

def find_discounted (s : String) : String := sorry

theorem empty_and_whitespace
  (s : String) (h : s.trim = "") :
  find_discounted s = "" := sorry

theorem specific_case_1 :
  find_discounted "15 20 60 75 80 100" = "15 60 75" := sorry

theorem specific_case_2 :
  find_discounted "9 9 12 12 12 15 16 20" = "9 9 12 15" := sorry

theorem specific_case_3 :
  find_discounted "0 0" = "0" := sorry

/-
info: '15 60 75'
-/
-- #guard_msgs in
-- #eval find_discounted "15 20 60 75 80 100"

/-
info: '9 9 12 15'
-/
-- #guard_msgs in
-- #eval find_discounted "9 9 12 12 12 15 16 20"

/-
info: '0'
-/
-- #guard_msgs in
-- #eval find_discounted "0 0"

-- Apps difficulty: introductory
-- Assurance level: unguarded