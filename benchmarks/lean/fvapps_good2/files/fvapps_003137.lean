-- <vc-preamble>
def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

def isLowerAscii (c : Char) : Bool :=
  97 ≤ c.toNat ∧ c.toNat ≤ 122
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform_word (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transform_word_preserves_length (s : String) :
  s.length = (transform_word s).length :=
sorry

theorem transform_word_chars_are_ascii_lower (s : String) :
  ∀ c ∈ (transform_word s).data, isLowerAscii c :=
sorry

theorem transform_word_vowel_consonant_mapping (s : String) :
  ∀ i, i < s.length →
    let pos : String.Pos := ⟨i⟩
    (isVowel (s.get pos) → ¬isVowel ((transform_word s).get pos)) ∧
    (¬isVowel (s.get pos) → isVowel ((transform_word s).get pos)) :=
sorry

theorem transform_word_deterministic (s : String) :
  transform_word s = transform_word s :=
sorry
-- </vc-theorems>