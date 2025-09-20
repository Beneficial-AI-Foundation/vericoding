-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def quicksum (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem quicksum_invalid_packets (s : String)
  (h : ∃ c ∈ s.data, c ≠ ' ' ∧ ¬(65 ≤ c.toNat ∧ c.toNat ≤ 90)) :
  quicksum s = 0 :=
  sorry
-- </vc-theorems>