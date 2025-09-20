-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def adFly_encoder (url : String) : String := sorry
def adFly_decoder (encoded : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip 
  (url : String) 
  (h : ∃ (s₁ s₂ : String), url = "http://" ++ s₁ ++ "." ++ s₂) :
  adFly_decoder (adFly_encoder url) = url := sorry

theorem invalid_input_returns_invalid
  (s : String)
  (h : ¬∃ (s₁ s₂ : String), s = "http://" ++ s₁ ++ "." ++ s₂) :
  adFly_decoder s = "Invalid" := sorry

theorem encoded_output_valid_base64
  (url : String)
  (h : ∃ (s₁ s₂ : String), url = "http://" ++ s₁ ++ "." ++ s₂) :
  ∀ c ∈ (adFly_encoder url).data,
    c ∈ ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
         'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
         'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
         'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
         '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '/', '='] := sorry
-- </vc-theorems>