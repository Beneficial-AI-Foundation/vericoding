-- <vc-helpers>
-- </vc-helpers>

def BUTTONS : List String := sorry
def presses (s : String) : Nat := sorry

/- For any string made up of valid keypad characters, the number of presses
    should be at least the length of the string, and each character should
    be present in one of the buttons -/

theorem keypad_chars_valid (s : String) :
  (∀ c ∈ s.data, ∃ button ∈ BUTTONS, c ∈ button.data) →
  presses s ≥ s.length := sorry

/- The number of presses required should be the same regardless of case -/

theorem case_insensitive (button : String) :
  button ∈ BUTTONS →
  presses button.toUpper = presses button.toLower := sorry

/- For strings containing only numbers and spaces, the number of presses
    should be at least the length of the string -/

theorem numeric_and_space_presses (s : String) :
  (∀ c ∈ s.data, c ∈ [' ', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) →
  presses s ≥ s.length := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval presses "LOL"

/-
info: 13
-/
-- #guard_msgs in
-- #eval presses "HOW R U"

/-
info: 47
-/
-- #guard_msgs in
-- #eval presses "WHERE DO U WANT 2 MEET L8R"

-- Apps difficulty: introductory
-- Assurance level: guarded