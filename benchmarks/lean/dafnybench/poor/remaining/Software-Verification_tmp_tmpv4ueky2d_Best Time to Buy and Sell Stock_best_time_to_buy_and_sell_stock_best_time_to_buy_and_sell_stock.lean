import Std

open Std.Do

/-!
{
  "name": "Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock_best_time_to_buy_and_sell_stock",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock_best_time_to_buy_and_sell_stock",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Finds the maximum profit that can be made by buying and selling stock once.
Input array represents stock prices over time.
Returns maximum possible profit.

@param prices Array of stock prices
@return Maximum profit possible
-/
def best_time_to_buy_and_sell_stock (prices : Array Int) : Int := sorry

/--
Specification for best_time_to_buy_and_sell_stock:
- Requires array length between 1 and 100000
- Requires all prices between 0 and 10000
- Ensures returned profit is maximum possible difference between any two prices
-/
theorem best_time_to_buy_and_sell_stock_spec (prices : Array Int) :
  1 ≤ prices.size ∧ prices.size ≤ 100000 ∧
  (∀ i, 0 ≤ i ∧ i < prices.size → 0 ≤ prices.get ⟨i⟩ ∧ prices.get ⟨i⟩ ≤ 10000) →
  let max_profit := best_time_to_buy_and_sell_stock prices
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < prices.size →
    max_profit ≥ prices.get ⟨j⟩ - prices.get ⟨i⟩ := sorry

end DafnyBenchmarks