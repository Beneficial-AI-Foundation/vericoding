-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validMorseChar (c : Char) : Bool :=
  sorry

def encryption (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encryption_morse_chars
  (s : String)
  (h : ∀ c, c ∈ s.data → c.isUpper)
  : ∀ c, c ∈ (encryption s).data → (c = '.' ∨ c = '-' ∨ c = ' ') :=
sorry

theorem encryption_word_separation
  (s : String)
  (h : ∀ c, c ∈ s.data → c.isUpper)
  : ((encryption s).splitOn "   ").length = (s.splitOn " ").length :=
sorry

theorem encryption_letter_separation
  (s : String)
  (h : ∀ c, c ∈ s.data → c.isUpper)
  : ∀ word, word ∈ ((encryption s).splitOn "   ") →
    ∀ letter, letter ∈ (word.splitOn " ") →
    letter.length > 0 :=
sorry

theorem encryption_case_insensitive
  (s : String)
  (h : ∀ c, c ∈ s.data → c.isUpper)
  : encryption s = encryption s.toLower ∧
    encryption s = encryption s.toUpper :=
sorry
-- </vc-theorems>