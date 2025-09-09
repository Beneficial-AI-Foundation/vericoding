-- <vc-helpers>
-- </vc-helpers>

def booleanToString (b : Bool) : String := sorry

theorem booleanToString_is_str (b : Bool) : 
  booleanToString b = toString b := by sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded