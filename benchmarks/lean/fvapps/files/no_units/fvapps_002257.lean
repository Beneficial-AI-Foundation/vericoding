-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_bad_prices (prices : List Int) : Nat := sorry

theorem count_bad_prices_non_negative (prices : List Int) :
  count_bad_prices prices ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_bad_prices_upper_bound (prices : List Int) : 
  count_bad_prices prices ≤ prices.length := sorry

theorem count_bad_prices_singleton (price : Int) :
  count_bad_prices [price] = 0 := sorry

theorem count_bad_prices_empty :
  count_bad_prices [] = 0 := sorry

theorem count_bad_prices_all_same (n : Nat) (x : Int) :
  count_bad_prices (List.replicate n x) = 0 := sorry
-- </vc-theorems>