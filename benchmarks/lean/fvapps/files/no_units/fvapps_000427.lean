-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode_at_index (s: String) (k: Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_at_index_is_letter {s: String} {k: Nat}
  (h1: k > 0) -- k is positive
  (h2: ∃ c, c ∈ s.data ∧ c.isAlpha) -- s contains at least one letter
  (h3: s.data ≠ [] → ¬(s.data[0]!.isDigit ∧ s.data[0]!.toNat ≥ 2)) -- s doesn't start with digit 2-9
  : ∃ c, (decode_at_index s k) = String.mk [c] ∧ c.isAlpha := 
  sorry

theorem decode_at_index_is_substring {s: String} {k: Nat}  
  (h1: k > 0)
  (h2: ∃ c, c ∈ s.data ∧ c.isAlpha)
  (h3: s.data ≠ [] → ¬(s.data[0]!.isDigit ∧ s.data[0]!.toNat ≥ 2))
  : ∃ c, (decode_at_index s k) = String.mk [c] ∧ c ∈ s.data := 
  sorry

theorem decode_at_index_first_letter {s: String}
  (h1: ∃ c, c ∈ s.data ∧ c.isAlpha)
  (h2: s.data ≠ [] → ¬(s.data[0]!.isDigit ∧ s.data[0]!.toNat ≥ 2))
  (h3: (s.data.filter Char.isAlpha) ≠ [])
  : decode_at_index s 1 = String.mk [(s.data.filter Char.isAlpha).head!] :=
  sorry
-- </vc-theorems>