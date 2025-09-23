-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isVowel (c : Char) : Bool := sorry

def vowel_recognition (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vowel_recognition_is_natural (s : String) :
  vowel_recognition s ≥ 0 :=
sorry

theorem case_insensitive (s : String) :
  vowel_recognition s.toUpper = vowel_recognition s.toLower :=
sorry
-- </vc-theorems>