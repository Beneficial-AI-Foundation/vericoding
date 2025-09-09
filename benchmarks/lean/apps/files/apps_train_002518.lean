-- <vc-helpers>
-- </vc-helpers>

def is_valid_regex (s : String) : Bool := sorry 

theorem any_string_input_returns_bool (s : String) :
  (is_valid_regex s = true) ∨ (is_valid_regex s = false) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible