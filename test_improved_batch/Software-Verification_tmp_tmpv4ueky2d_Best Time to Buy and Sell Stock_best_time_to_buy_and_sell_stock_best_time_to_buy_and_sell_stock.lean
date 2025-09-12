/-
  Port of Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock_best_time_to_buy_and_sell_stock.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def best_time_to_buy_and_sell_stock (prices : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem best_time_to_buy_and_sell_stock_spec (prices : Array Int) (max_profit : Int) :=
  (h_0 : 1 ≤ prices.size ≤ 100000)
  (h_1 : ∀ i :: 0 ≤ i < prices.size → 0 ≤ prices[i]! ≤ 10000)
  : ∀ i, j :: 0 ≤ i < j < prices.size → max_profit ≥ prices[j]! - prices[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks