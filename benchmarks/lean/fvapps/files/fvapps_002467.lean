-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_divisions (l : List String) : List String := sorry

theorem valid_divisions {test_cases : List String} 
  (h : ∀ tc ∈ test_cases, ∃ a b : Int, tc = toString a ++ " " ++ toString b) :
  let results := process_divisions test_cases
  -- Length preservation
  results.length = test_cases.length ∧
  -- Each result matches expected division behavior
  ∀ i : Fin test_cases.length,
    let tc := test_cases[i]
    let parts := tc.splitOn " "
    let a := parts[0]!
    let b := parts[1]!
    if (String.toInt? b = some 0) then
      results[i]! = "Error Code: integer division or modulo by zero"
    else
      results[i]! = toString ((String.toInt? a).get! / (String.toInt? b).get!) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_first_number {test_cases : List String}
  (h : ∀ tc ∈ test_cases, ∃ inv valid : String,
    tc = inv ++ " " ++ valid ∧ 
    String.toInt? inv = none ∧
    String.toInt? valid ≠ none) :
  let results := process_divisions test_cases
  results.length = test_cases.length ∧
  ∀ r ∈ results, (r.startsWith "Error Code:") := sorry

theorem invalid_second_number {test_cases : List String}
  (h : ∀ tc ∈ test_cases, ∃ valid inv : String,
    tc = valid ++ " " ++ inv ∧
    String.toInt? valid ≠ none ∧
    String.toInt? inv = none) :
  let results := process_divisions test_cases
  results.length = test_cases.length ∧
  ∀ r ∈ results, (r.startsWith "Error Code:") := sorry
-- </vc-theorems>