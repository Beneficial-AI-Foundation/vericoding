-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def caesar_crypto_encode (text : String) (shift : Int) : String := sorry

theorem caesar_length_preservation (text : String) (shift : Int) :
  String.length (caesar_crypto_encode text shift) ≤ String.length text := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem caesar_length_strip (text : String) (shift : Int) :
  String.length (String.trim (caesar_crypto_encode text shift)) = String.length (caesar_crypto_encode text shift) := sorry

theorem caesar_nonletters_preserved (text : String) (shift : Int) (c : Char) :
  ¬(c.isAlpha) ∧ c ≠ ' ' →
  (String.contains (caesar_crypto_encode text shift) c ↔ String.contains (String.trim text) c) := sorry

theorem caesar_shift_wrapping (text : String) (shift : Int) :
  caesar_crypto_encode text shift = caesar_crypto_encode text (shift % 52) := sorry

theorem caesar_identity_shift (text : String) :
  caesar_crypto_encode text 0 = String.trim text ∨ text.all Char.isWhitespace := sorry

theorem caesar_reverse_shift (text : String) (shift : Int) :
  String.trim (caesar_crypto_encode (caesar_crypto_encode text shift) (-shift)) = String.trim text ∨ 
  text.all Char.isWhitespace := sorry

theorem caesar_empty_and_whitespace_1 :
  caesar_crypto_encode "" 1 = "" := sorry

theorem caesar_empty_and_whitespace_2 :
  caesar_crypto_encode " \t\n" 1 = "" := sorry
-- </vc-theorems>