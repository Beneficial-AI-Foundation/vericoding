-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def keyword_cipher (text : String) (keyword : String) : String := sorry

theorem keyword_cipher_identity (text : String) :
  keyword_cipher text "abcdefghijklmnopqrstuvwxyz" = text.toLower := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem keyword_cipher_length (text : String) (keyword : String) :
  (keyword_cipher text keyword).length = text.length := sorry

theorem keyword_cipher_lowercase (text : String) (keyword : String) :
  (keyword_cipher text keyword).toLower = keyword_cipher text keyword := sorry

theorem keyword_cipher_preserves_spaces (text : String) (keyword : String) (i : String.Pos) :
  text.get i = ' ' →
  (keyword_cipher text keyword).get i = ' ' := sorry
-- </vc-theorems>