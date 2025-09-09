def encodeAscii (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def decodeAsciiMessage (s : String) : String :=
  sorry

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

/-
info: 'Hello World'
-/
-- #guard_msgs in
-- #eval decode_ascii_message "721011081081113287111114108100"

/-
info: 'Welcome to India'
-/
-- #guard_msgs in
-- #eval decode_ascii_message "871011089911110910132116111327311010010597"

-- Apps difficulty: interview
-- Assurance level: unguarded