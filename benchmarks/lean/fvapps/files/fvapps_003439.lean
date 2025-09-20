-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (message : String) (key : String) : String := sorry
def decode (message : String) (key : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_key_chars_unchanged (message : String) (key : String) (i : String.Pos) :
  let key_chars := (key.toLower ++ key.toUpper).toList.toArray
  ¬(key_chars.contains (message.get i)) →
  (encode message key).get i = message.get i := sorry

theorem consistent_encoding (message key : String) :
  encode message key = encode message key := sorry
-- </vc-theorems>