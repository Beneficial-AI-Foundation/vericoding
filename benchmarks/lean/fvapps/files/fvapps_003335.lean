-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidKey (k : String) : Bool :=
  sorry

def encode (text key : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_preserves_non_letters (text key : String) :
  isValidKey key → ∀ i, ¬(text.get! i).isAlpha →
  (encode text key).get! i = text.get! i :=
sorry

theorem encode_preserves_case (text key : String) :
  isValidKey key → ∀ i,
  let c := text.get! i
  let e := (encode text key).get! i
  c.isAlpha → (c.isUpper = e.isUpper) :=
sorry

theorem encode_duplicate_key_chars (text key : String) :
  isValidKey key →
  encode text key = encode text (String.mk (key.data.eraseDups)) :=
sorry
-- </vc-theorems>