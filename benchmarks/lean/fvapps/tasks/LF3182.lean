-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>