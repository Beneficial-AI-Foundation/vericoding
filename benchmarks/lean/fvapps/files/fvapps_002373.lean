-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_profit (prices : List Nat) : Nat := sorry

theorem max_profit_nonnegative (prices : List Nat) :
  max_profit prices ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_profit_empty_or_singleton {prices : List Nat} :
  prices.length ≤ 1 → max_profit prices = 0 := sorry 

theorem max_profit_bounded_by_extremes {prices : List Nat} {i j : Nat} 
  (h₁ : i < prices.length) (h₂ : j < prices.length) :
  max_profit prices ≤ prices[j]'h₂ - prices[i]'h₁ := sorry

theorem max_profit_optimal_for_each_buy_day {prices : List Nat} {i : Nat} 
  (h₁ : i < prices.length) (j : Nat) (h₂ : i + 1 + j < prices.length) :
  max_profit prices ≥ prices[i + 1 + j]'h₂ - prices[i]'h₁ := sorry

theorem max_profit_decreasing {prices : List Nat} {i j : Nat} 
  (h₁ : i < prices.length) (h₂ : j < prices.length)
  (h_len : prices.length > 1)
  (h_sorted : i < j → prices[i]'h₁ ≥ prices[j]'h₂) :
  max_profit prices = 0 := sorry

theorem max_profit_increasing {prices : List Nat} {i j : Nat}
  (h₁ : i < prices.length) (h₂ : j < prices.length)
  (h_len : prices.length > 1)
  (h_sorted : i < j → prices[i]'h₁ ≤ prices[j]'h₂)
  (h_last : prices.length - 1 < prices.length)
  (h_zero : 0 < prices.length) :
  max_profit prices = prices[prices.length-1]'h_last - prices[0]'h_zero := sorry
-- </vc-theorems>