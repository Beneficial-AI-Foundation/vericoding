-- <vc-helpers>
-- </vc-helpers>

def is_letter (s : String) : Bool := sorry

theorem letter_length_check : 
  ∀ s : String, s.length ≠ 1 → ¬(is_letter s) := sorry

theorem letter_matches_ascii (s : String) (h: s.length = 1):
  is_letter s = s.data[0]!.isAlpha := sorry

theorem letters_are_letters :
  ∀ c : Char, c.isAlpha → is_letter c.toString := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_letter ""

/-
info: True
-/
-- #guard_msgs in
-- #eval is_letter "a"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_letter "X"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_letter "7"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_letter "ab"

-- Apps difficulty: introductory
-- Assurance level: unguarded