-- <vc-helpers>
-- </vc-helpers>

def is_isogram (s : String) : Bool := sorry

theorem isogram_output_is_bool :
  ∀ s : String, is_isogram s = true ∨ is_isogram s = false := sorry

theorem non_string_input_is_false :
  is_isogram "" = false := sorry

theorem case_insensitive :
  ∀ s : String, is_isogram s = is_isogram s.toLower := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_isogram "Dermatoglyphics"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_isogram None

/-
info: True
-/
-- #guard_msgs in
-- #eval is_isogram "aabbccddeeffgg"

-- Apps difficulty: introductory
-- Assurance level: unguarded