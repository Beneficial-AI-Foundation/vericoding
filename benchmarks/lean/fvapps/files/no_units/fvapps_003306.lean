-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_parse (x : String) : String := sorry

theorem non_string_input_error (x : Int) :
  string_parse (toString x) = "Please enter a valid string" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_property {s : String} :
  let result := string_parse s
  let cleaned_result := result.replace "[" "" |>.replace "]" ""
  result = "Please enter a valid string" ∨ cleaned_result.length ≤ s.length := sorry

theorem preserves_order {s : String} {c : Char} :
  let result := string_parse s
  let cleaned_result := result.replace "[" "" |>.replace "]" ""
  result = "Please enter a valid string" ∨ cleaned_result.contains c → s.contains c := sorry
-- </vc-theorems>