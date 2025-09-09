-- <vc-helpers>
-- </vc-helpers>

def isVowel (c : Char) : Bool := sorry

def vowel_recognition (s : String) : Nat := sorry

theorem vowel_recognition_is_natural (s : String) :
  vowel_recognition s ≥ 0 :=
sorry

theorem case_insensitive (s : String) :
  vowel_recognition s.toUpper = vowel_recognition s.toLower :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval vowel_recognition "bbbb"

/-
info: 16
-/
-- #guard_msgs in
-- #eval vowel_recognition "baceb"

/-
info: 35
-/
-- #guard_msgs in
-- #eval vowel_recognition "aeiou"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible