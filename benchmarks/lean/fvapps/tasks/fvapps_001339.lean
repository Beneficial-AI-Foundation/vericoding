-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_expected_picks (n q : Nat) : Float := sorry

theorem expected_picks_positive (n q : Nat)  
  (h1 : n > 0) (h2 : q > 0) (h3 : n ≤ 1000) (h4 : q ≤ 1000) :
  calculate_expected_picks n q > 0 ∧ calculate_expected_picks n q ≥ Float.ofNat q := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expected_picks_upper_bound (n q : Nat) 
  (h1 : n > 0) (h2 : q > 0) (h3 : n ≤ 1000) (h4 : q ≤ 1000) :
  calculate_expected_picks n q ≤ Float.ofNat (n + q) := sorry

theorem expected_picks_simple_cases :
  (calculate_expected_picks 1 1 - 1.5).abs < 0.000001 ∧ 
  (calculate_expected_picks 2 2 - 3.3333333333).abs < 0.000001 := sorry
-- </vc-theorems>