def validMorseChar (c : Char) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def encryption (s : String) : String :=
  sorry

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

/-
info: '.... . .-.. .-.. ---   .-- --- .-. .-.. -..'
-/
-- #guard_msgs in
-- #eval encryption "HELLO WORLD"

/-
info: '... --- ...'
-/
-- #guard_msgs in
-- #eval encryption "SOS"

/-
info: '- .... .   --.- ..- .. -.-. -.-   -... .-. --- .-- -.   ..-. --- -..-'
-/
-- #guard_msgs in
-- #eval encryption "THE QUICK BROWN FOX"

-- Apps difficulty: introductory
-- Assurance level: unguarded