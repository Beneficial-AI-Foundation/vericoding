-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sale_hotdogs (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hotdog_prices_monotonic {n: Nat} (h: n > 1) : 
  sale_hotdogs n / n ≤ sale_hotdogs (n-1) / (n-1) :=
sorry

theorem hotdog_price_tiers_less_than_5 {n: Nat} (h: n > 0 ∧ n < 5) :
  sale_hotdogs n = n * 100 :=
sorry

theorem hotdog_price_tiers_less_than_10 {n: Nat} (h: n ≥ 5 ∧ n < 10) :
  sale_hotdogs n = n * 95 :=
sorry 

theorem hotdog_price_tiers_10_or_more {n: Nat} (h: n ≥ 10) :
  sale_hotdogs n = n * 90 :=
sorry
-- </vc-theorems>