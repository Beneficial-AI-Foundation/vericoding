-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 1.5
-/
-- #guard_msgs in
-- #eval parse_float "1.5"

/-
info: -123.45
-/
-- #guard_msgs in
-- #eval parse_float "-123.45"

/-
info: 0.0
-/
-- #guard_msgs in
-- #eval parse_float "0.0"

/-
info: None
-/
-- #guard_msgs in
-- #eval parse_float "abc"

/-
info: None
-/
-- #guard_msgs in
-- #eval parse_float "12a34"

/-
info: None
-/
-- #guard_msgs in
-- #eval parse_float ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded