-- <vc-preamble>
def MORSE_CHARS := [
  ".-", "-...", "-.-.", "-..", ".", "..-.", "--.", "....", "..", 
  ".---", "-.-", ".-..", "--", "-.", "---", ".--.", "--.-", ".-.", 
  "...", "-", "..-", "...-", ".--", "-..-", "-.--", "--..", "-----",
  ".----", "..---", "...--", "....-", ".....", "-....", "--...", 
  "---..", "----."
]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode (s : String) : String := sorry

def splitString (s : String) (sep : Char) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_preserves_word_count (morse_words : List (List String))
  (h_valid : ∀ w ∈ morse_words, ∀ c ∈ w, c ∈ MORSE_CHARS)
  (morse_string := String.intercalate "  " (morse_words.map (String.intercalate " "))) :
  (splitString (decode morse_string) ' ').length = morse_words.length := sorry

theorem decode_returns_alphanumeric (morse_words : List (List String))
  (h_valid : ∀ w ∈ morse_words, ∀ c ∈ w, c ∈ MORSE_CHARS)
  (morse_string := String.intercalate "  " (morse_words.map (String.intercalate " "))) :
  ∀ c ∈ (decode morse_string).data, c.isAlphanum ∨ c = ' ' := sorry

theorem decode_empty_string :
  decode "" = "" := sorry

theorem decode_singleton_space :
  decode " " = " " := sorry
-- </vc-theorems>