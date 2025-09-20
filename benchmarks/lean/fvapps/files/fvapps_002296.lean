-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def first_unique_char (s : String) : Int := sorry

theorem empty_string_returns_negative_one : 
  first_unique_char "" = -1 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_returns_zero (c : Char) 
  (h : 'a' ≤ c ∧ c ≤ 'z') : 
  first_unique_char (String.mk [c]) = 0 := 
sorry
-- </vc-theorems>