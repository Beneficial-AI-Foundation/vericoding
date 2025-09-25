-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def equal_to_24 (a b c d : Int) : String := sorry

def isValidResult (result : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_to_24_valid_output 
  (a b c d : Int) 
  (h1 : 1 ≤ a ∧ a ≤ 13) 
  (h2 : 1 ≤ b ∧ b ≤ 13)
  (h3 : 1 ≤ c ∧ c ≤ 13)
  (h4 : 1 ≤ d ∧ d ≤ 13) :
  isValidResult (equal_to_24 a b c d) := sorry

theorem equal_numbers_valid_output
  (n : Int)
  (h : 1 ≤ n ∧ n ≤ 100) :
  isValidResult (equal_to_24 n n n n) := sorry

theorem impossible_cases_zero :
  equal_to_24 0 0 0 0 = "It's not possible!" := sorry

theorem impossible_cases_negative :
  equal_to_24 (-1) (-1) (-1) (-1) = "It's not possible!" := sorry

theorem impossible_cases_large :
  equal_to_24 1000 1000 1000 1000 = "It's not possible!" := sorry

theorem division_by_zero :
  isValidResult (equal_to_24 0 1 2 3) := sorry
-- </vc-theorems>