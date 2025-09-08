/-
Write a function that will encrypt a given sentence into International Morse Code, both the input and out puts will be strings.

Characters should be separated by a single space.
Words should be separated by a triple space.

For example, "HELLO WORLD" should return -> ".... . .-.. .-.. ---   .-- --- .-. .-.. -.."

To find out more about Morse Code follow this link: https://en.wikipedia.org/wiki/Morse_code

A preloaded object/dictionary/hash called CHAR_TO_MORSE will be provided to help convert characters to Morse Code.
-/

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