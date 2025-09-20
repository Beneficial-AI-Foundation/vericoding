-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_scrap (rates: List Float) (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scrap_result_is_at_least_base (rates: List Float) (n: Nat) : calculate_scrap rates n ≥ n * 50 := 
  sorry

theorem scrap_monotonic_with_rates (rates: List Float) (n: Nat) (i: Nat) (hi: i < rates.length) :
  calculate_scrap (rates.take i) n ≤ calculate_scrap rates n :=
  sorry

theorem zero_scrap_is_base (rates: List Float) (n: Nat) (h: ∀ r ∈ rates, r = 0) :
  calculate_scrap rates n = n * 50 :=
  sorry

theorem empty_rates_is_base (n: Nat) :
  calculate_scrap [] n = n * 50 :=
  sorry
-- </vc-theorems>