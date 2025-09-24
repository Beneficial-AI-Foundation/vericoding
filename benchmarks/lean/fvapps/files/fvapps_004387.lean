-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode (s : String) : String := sorry

theorem decode_twice (s : String) 
  (h : ∀ c ∈ s.data, c.toNat ≥ 48 ∧ c.toNat ≤ 57) : -- ensure only digits 0-9
  decode (decode s) = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_preserves_length (s : String) 
  (h : ∀ c ∈ s.data, c.toNat ≥ 48 ∧ c.toNat ≤ 57) :
  (decode s).length = s.length := sorry

theorem decode_outputs_digits (s : String) 
  (h : ∀ c ∈ s.data, c.toNat ≥ 48 ∧ c.toNat ≤ 57) 
  (h2 : s.length > 0) :
  ∀ c ∈ (decode s).data, c.toNat ≥ 48 ∧ c.toNat ≤ 57 := sorry

theorem decode_empty : decode "" = "" := sorry

theorem decode_consistent_mapping (s : String)
  (h : ∀ c ∈ s.data, c.toNat ≥ 48 ∧ c.toNat ≤ 57)
  (h2 : s.length ≥ 2) :
  ∀ (i j : String.Pos), i.1 < j.1 → j.1 < s.length → 
    s.get i = s.get j → 
    (decode s).get i = (decode s).get j := sorry
-- </vc-theorems>