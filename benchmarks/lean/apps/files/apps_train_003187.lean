-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def booleanToString (b : Bool) : String := sorry

theorem booleanToString_is_str (b : Bool) : 
  booleanToString b = toString b := by sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 'True'
-/
-- #guard_msgs in
-- #eval boolean_to_string True

/-
info: 'False'
-/
-- #guard_msgs in
-- #eval boolean_to_string False
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded