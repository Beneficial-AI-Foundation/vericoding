-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 'aa[aa]bbcdeff[fffff]g'
-/
-- #guard_msgs in
-- #eval string_parse "aaaabbcdefffffffg"

/-
info: 'Please enter a valid string'
-/
-- #guard_msgs in
-- #eval string_parse 3

/-
info: 'aAAabbcdeFF[F]ff[ff]g'
-/
-- #guard_msgs in
-- #eval string_parse "aAAabbcdeFFFffffg"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded