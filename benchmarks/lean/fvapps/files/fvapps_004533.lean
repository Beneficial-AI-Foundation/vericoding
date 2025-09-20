-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse_float (s : String) : Option Float := sorry 

theorem parse_valid_float (f : Float) : 
  parse_float (toString f) = some f := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parse_invalid_string {s : String} :
  (∀ f : Float, toString f ≠ s) → parse_float s = none := sorry 

theorem parse_empty_string :
  parse_float "" = none := sorry
-- </vc-theorems>