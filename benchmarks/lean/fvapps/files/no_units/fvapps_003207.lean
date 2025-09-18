-- <vc-preamble>
def going (n : Nat) : Float := sorry

theorem going_range (n : Nat) : 
  1 ≤ going n ∧ going n ≤ 2 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_series (n : Nat) : Float := sorry

theorem going_matches_calc_series (n : Nat) :
  n ≥ 1 → n ≤ 100 → Float.abs (going n - calc_series n) < 0.000001 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem going_decimal_places (n : Nat) :
  ∃ k : Nat, k ≤ 6 ∧ going n * Float.ofNat (10^k) = Float.floor (going n * Float.ofNat (10^k)) := sorry

theorem going_specific_values :
  going 1 = 1.0 ∧ going 5 = 1.275 := sorry
-- </vc-theorems>