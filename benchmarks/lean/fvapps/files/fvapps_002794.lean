-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_vowel (s : String) : Bool := sorry

theorem is_vowel_length_property {s : String} :
  is_vowel s → s.length = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_vowel_case_insensitive {s : String} :
  s.length = 1 → is_vowel s = is_vowel s.toLower := sorry

theorem is_vowel_set_membership {s : String} :
  is_vowel s → s.toLower = "a" ∨ s.toLower = "e" ∨ s.toLower = "i" ∨ s.toLower = "o" ∨ s.toLower = "u" := sorry

theorem non_vowel_property {s : String} :
  s.length = 1 → (s.toLower ≠ "a" ∧ s.toLower ≠ "e" ∧ s.toLower ≠ "i" ∧ s.toLower ≠ "o" ∧ s.toLower ≠ "u") → ¬is_vowel s := sorry

theorem vowels_are_true_property {v : String} :
  (v = "a" ∨ v = "e" ∨ v = "i" ∨ v = "o" ∨ v = "u" ∨ 
   v = "A" ∨ v = "E" ∨ v = "I" ∨ v = "O" ∨ v = "U") → 
  is_vowel v := sorry

theorem multiple_chars_are_false {s : String} :
  s.length ≥ 2 → ¬is_vowel s := sorry
-- </vc-theorems>