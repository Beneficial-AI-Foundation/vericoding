-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_stock_profit_with_cooldown (prices : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_single_price_zero (prices : List Nat) 
  (h : prices.length ≤ 1) : 
  max_stock_profit_with_cooldown prices = 0 :=
  sorry

theorem result_always_non_negative (prices : List Nat) :
  max_stock_profit_with_cooldown prices ≥ 0 :=
  sorry

theorem decreasing_prices_zero_profit {prices : List Nat}
  (h₁ : prices.length ≥ 2)
  (h₂ : ∀ i j, i < j → j < prices.length → prices[i]! ≥ prices[j]!) :
  max_stock_profit_with_cooldown prices = 0 :=
  sorry

theorem profit_bounded_by_adjacent_diffs {prices : List Nat}
  (h : prices.length ≥ 2) :
  max_stock_profit_with_cooldown prices ≤ 
    (List.zip prices prices.tail!).foldl
      (fun acc (p : Nat × Nat) => acc + max (p.2 - p.1) 0)
      0 :=
  sorry

theorem repeated_list_profit_geq {prices : List Nat}
  (h : prices.length ≥ 1) :
  max_stock_profit_with_cooldown (prices ++ prices) ≥ 
  max_stock_profit_with_cooldown prices :=
  sorry
-- </vc-theorems>