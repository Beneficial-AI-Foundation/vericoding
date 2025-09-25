-- <vc-preamble>
def isLower (c : Char) : Bool := sorry
def isUpper (c : Char) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toLower (c : Char) : Char := sorry
def charInString (c : Char) (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip (cipher : VigenereCipher) (text : String) :
  cipher.decode (cipher.encode text) = text := sorry

theorem case_preservation (cipher : VigenereCipher) (text encoded : String)
  (h1 : encoded = cipher.encode text) 
  (h2 : ∃ i c1 c2, text.get? i = some c1 ∧ encoded.get? i = some c2 ∧ charInString (toLower c1) cipher.alphabet) :
  ∀ i c1 c2, text.get? i = some c1 → encoded.get? i = some c2 → charInString (toLower c1) cipher.alphabet →
  isUpper c1 = isUpper c2 := sorry 

theorem special_char_preservation (cipher : VigenereCipher) (text encoded : String)
  (h1 : encoded = cipher.encode text)
  (h2 : ∃ i c1 c2, text.get? i = some c1 ∧ encoded.get? i = some c2 ∧ ¬charInString (toLower c1) cipher.alphabet) :
  ∀ i c1 c2, text.get? i = some c1 → encoded.get? i = some c2 → ¬charInString (toLower c1) cipher.alphabet →
  c1 = c2 := sorry

theorem empty_string (cipher : VigenereCipher) :
  cipher.encode "" = "" ∧ cipher.decode "" = "" := sorry
-- </vc-theorems>