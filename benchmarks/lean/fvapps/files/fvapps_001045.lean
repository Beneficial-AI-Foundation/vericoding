-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_hits_needed (s w1 w2 w3 : Nat) : Nat := sorry

theorem min_hits_needed_bounded (s w1 w2 w3 : Nat) :
  s > 0 → w1 > 0 → w2 > 0 → w3 > 0 → 
  1 ≤ min_hits_needed s w1 w2 w3 ∧ min_hits_needed s w1 w2 w3 ≤ 3 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_hits_needed_single_hit (s w1 w2 w3 : Nat) :
  s > 0 → w1 > 0 → w2 > 0 → w3 > 0 →
  s ≥ w1 + w2 + w3 →
  min_hits_needed s w1 w2 w3 = 1 := sorry

theorem min_hits_needed_two_hits (s w1 w2 w3 : Nat) :
  s > 0 → w1 > 0 → w2 > 0 → w3 > 0 →
  (s ≥ w1 + w2 ∨ s ≥ w2 + w3) →
  min_hits_needed s w1 w2 w3 ≤ 2 := sorry
-- </vc-theorems>