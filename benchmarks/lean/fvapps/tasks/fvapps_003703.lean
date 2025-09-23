-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def guess_my_number (guess : String) (target : String := "123-456-7890") : String := sorry

/- For any numeric guess, the result should be a properly formatted phone number string -/
-- </vc-definitions>

-- <vc-theorems>
theorem guess_result_format (guess : String) : 
  let result := guess_my_number guess
  (String.length result = 12) ∧ 
  (result.data.filter (· = '-')).length = 2 ∧
  (∀ c, c ∈ result.data → c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ 
                          c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' ∨ 
                          c = '#' ∨ c = '-') := sorry

/- An empty guess should return all digits masked -/

theorem empty_guess_masks_all (target : String) :
  guess_my_number "" target = "###-###-####" := sorry

/- Result maintains proper phone number format with dashes in correct positions -/

theorem result_dash_positions (guess : String) (target : String) :
  let result := guess_my_number guess target
  let data := result.data
  String.length result = 12 ∧
  data[3]! = '-' ∧ 
  data[7]! = '-' := sorry
-- </vc-theorems>