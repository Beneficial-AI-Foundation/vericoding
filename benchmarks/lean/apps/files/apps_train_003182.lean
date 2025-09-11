-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_missing_number (s : String) : Nat := sorry 

theorem find_missing_number_non_negative (s : String) : 
  find_missing_number s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_missing_number_invalid (s : String) 
  (h : ¬(s.trim.replace " " "").all Char.isDigit) :
  find_missing_number s = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_missing_number "1 2 3 4"

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_missing_number "1 2 4"

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_missing_number "1 2 a"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible