-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (n : Nat) (s : String) : String := sorry
def decode (s : String) : String := sorry

/- For any number n and text, decoding after encoding returns original text -/
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip (n : Nat) (text : String) :
  decode (encode n text) = text := sorry
-- </vc-theorems>