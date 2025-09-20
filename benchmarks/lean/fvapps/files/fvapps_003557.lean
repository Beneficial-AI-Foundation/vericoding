-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ipv4_address (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_ip_addresses (a b c d : Nat) 
  (h₁ : a ≤ 255) (h₂ : b ≤ 255) (h₃ : c ≤ 255) (h₄ : d ≤ 255) :
  ipv4_address (s!"{a}.{b}.{c}.{d}") = true :=
sorry

theorem rejects_large_numbers (n : Nat) (h : n ≥ 256) :
  ipv4_address (s!"127.0.0.{n}") = false :=
sorry

theorem rejects_invalid_characters (s : String) 
  (h : ∃ c ∈ s.toList, ¬c.isDigit ∧ c ≠ '.') :
  ipv4_address s = false :=
sorry

theorem rejects_wrong_segment_count (n : Nat) 
  (h₁ : n > 0) (h₂ : n ≠ 4) :
  ipv4_address (String.intercalate "." (List.replicate n "0")) = false :=
sorry

theorem rejects_leading_zeros (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 99) :
  ipv4_address (s!"127.0.0.{String.mk (List.replicate (3 - String.length (toString n)) '0' ++ String.toList (toString n))}") = false :=
sorry

theorem rejects_whitespace (s : String) 
  (h : s.length > 0) :
  ipv4_address (s!"127.0.0.1{s}") = false :=
sorry
-- </vc-theorems>