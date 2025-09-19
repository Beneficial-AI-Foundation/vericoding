-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstNonRepeatingLetter (s : String) : String := sorry 

theorem empty_string_returns_empty : 
  firstNonRepeatingLetter "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_in_original_string {s result : String} :
  firstNonRepeatingLetter s = result → 
  result ≠ "" →
  ∃ i, String.get s i = String.get result 0 := sorry

theorem case_sensitivity_preserved {s result : String} :
  firstNonRepeatingLetter s = result →
  result ≠ "" →
  let lowerChar := String.get (String.toLower result) 0
  ∃ i, String.get (String.toLower s) i = lowerChar ∧
       String.get s i = String.get result 0 := sorry

theorem returns_first_nonrepeating {s result : String} :
  firstNonRepeatingLetter s = result →
  result ≠ "" →
  let lowerChar := String.get (String.toLower result) 0
  ∃ idx, String.get s idx = String.get result 0 ∧
         (∀ i < idx, ∃ j ≠ i, 
           String.get (String.toLower s) i = String.get (String.toLower s) j) := sorry
-- </vc-theorems>