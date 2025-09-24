-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def over_the_road (address n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem over_the_road_in_range (address n : Nat) :
  address > 0 → address ≤ 2*n → 
  1 ≤ over_the_road address n ∧ over_the_road address n ≤ 2*n :=
  sorry

theorem over_the_road_involution (address n : Nat) :
  address > 0 → address ≤ 2*n →
  over_the_road (over_the_road address n) n = address :=
  sorry 

theorem over_the_road_sum (address n : Nat) :
  address > 0 → address ≤ 2*n →
  address + over_the_road address n = 2*n + 1 :=
  sorry

theorem over_the_road_parity (address n : Nat) :
  address > 0 → address ≤ 2*n →
  (address % 2 = 0 ↔ over_the_road address n % 2 = 1) :=
  sorry

theorem over_the_road_examples :
  over_the_road 1 3 = 6 ∧ 
  over_the_road 3 3 = 4 ∧ 
  over_the_road 2 3 = 5 :=
  sorry
-- </vc-theorems>