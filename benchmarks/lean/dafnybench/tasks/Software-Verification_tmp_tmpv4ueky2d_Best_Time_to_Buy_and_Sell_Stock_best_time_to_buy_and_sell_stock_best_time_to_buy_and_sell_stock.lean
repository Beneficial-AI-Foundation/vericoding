-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def best_time_to_buy_and_sell_stock (prices : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem best_time_to_buy_and_sell_stock_spec (prices : Array Int) :
1 ≤ prices.size ∧ prices.size ≤ 100000 ∧
(∀ i, 0 ≤ i ∧ i < prices.size → 0 ≤ prices[i]! ∧ prices[i]! ≤ 10000) →
let max_profit := best_time_to_buy_and_sell_stock prices
∀ i j, 0 ≤ i ∧ i < j ∧ j < prices.size →
max_profit ≥ prices[j]! - prices[i]! :=
sorry
-- </vc-theorems>