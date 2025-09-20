-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encodeAscii (s : String) : String :=
  sorry

def decodeAsciiMessage (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_matches_input {s : String}
    (h1 : s ≠ "")
    (h2 : ∀ c ∈ s.data, 32 ≤ c.toNat ∧ c.toNat ≤ 126) :
    decodeAsciiMessage (encodeAscii s) = s :=
sorry

theorem decoded_chars_in_ascii_range {s : String}
    (h1 : s ≠ "")
    (h2 : ∀ c ∈ s.data, 32 ≤ c.toNat ∧ c.toNat ≤ 126) :
    ∀ c ∈ (decodeAsciiMessage (encodeAscii s)).data,
      32 ≤ c.toNat ∧ c.toNat ≤ 126 :=
sorry

theorem encoded_is_numeric {s : String}
    (h1 : s ≠ "")
    (h2 : ∀ c ∈ s.data, 32 ≤ c.toNat ∧ c.toNat ≤ 126) :
    ∀ c ∈ (encodeAscii s).data, c.isDigit :=
sorry
-- </vc-theorems>