-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vowel_2_index (s : String) : String := sorry

def isVowel (c : Char) : Bool :=
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u' ∨ 
  c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U'
-- </vc-definitions>

-- <vc-theorems>
theorem vowels_replaced_with_position {s : String} :
  ∀ (i : Nat) (h : i < s.length), 
  isVowel (s.data[i]'h) →
  ∃ (h' : 0 < (toString (i + 1)).length),
  String.contains (vowel_2_index s) ((toString (i + 1)).data[0]'h') := sorry

theorem empty_string :
  vowel_2_index "" = "" := sorry

theorem consonants_only_unchanged {s : String} :
  (∀ c ∈ s.data, ¬isVowel c) →
  vowel_2_index s = s := sorry

theorem punctuation_unchanged {s : String} :
  (∀ c ∈ s.data, c = ' ' ∨ c = '.' ∨ c = ',' ∨ c = '!' ∨ c = '?') →
  vowel_2_index s = s := sorry
-- </vc-theorems>