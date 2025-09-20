-- <vc-preamble>
def LOWER : String :=
  "abcdefghijklmnopqrstuvwxyz"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (message : String) (key : String) (shift : Int) : String :=
  sorry

def decode (message : String) (key : String) (shift : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip
  {message key : String} {shift : Int}
  (h1 : ∀ c ∈ message.data, c.toString ∈ LOWER.data.map toString)
  (h2 : key.length > 0)
  (h3 : ∀ c ∈ key.data, c.toString ∈ LOWER.data.map toString) :
  decode (encode message key shift) key shift = message :=
sorry

theorem non_alphabet_chars_unchanged
  {message key : String} {shift : Int}
  (h1 : key.length > 0)
  (h2 : ∀ c ∈ key.data, c.toString ∈ LOWER.data.map toString) :
  ∀ (i : Nat) (h3 : i < message.length),
    (message.data.get ⟨i, h3⟩) ∉ LOWER.data →
    (encode message key shift).data.get ⟨i, sorry⟩ = message.data.get ⟨i, h3⟩ :=
sorry
-- </vc-theorems>