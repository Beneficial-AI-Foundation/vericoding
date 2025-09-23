-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def who_is_paying (name : String) : List String := sorry

theorem who_is_paying_result_properties (name : String) :
  let result := who_is_paying name
  -- Result has first element equal to full name
  result.head! = name ∧ 
  -- Result length is either 1 or 2
  (result.length = 1 ∨ result.length = 2) ∧
  -- For strings > 2 chars, length is 2 and second element is first 2 chars
  (name.length > 2 → 
    result.length = 2 ∧ 
    result.get! 1 = name.take 2) ∧
  -- For strings ≤ 2 chars, length is 1
  (name.length ≤ 2 → result.length = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem who_is_paying_long_strings (name : String) (h : name.length ≥ 3) :
  let result := who_is_paying name
  result.length = 2 ∧ 
  result.get! 1 = name.take 2 := sorry

theorem who_is_paying_short_strings (name : String) (h : name.length ≤ 2) :
  let result := who_is_paying name
  result.length = 1 ∧
  result.head! = name := sorry
-- </vc-theorems>