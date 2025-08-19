/* code modified by LLM (iteration 1): Fixed compilation error by removing invalid text and properly formatting as Dafny comments */
// The key insight is that the postcondition `ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]` means that `max_profit` must be at least as large as any possible profit from buying at day `i` and selling at day `j` (where `i < j`).
//
// This is the classic "maximum subarray difference" problem where we want to find the maximum value of `prices[j] - prices[i]` for `i < j`. The efficient solution is to track the minimum price seen so far and the maximum profit achievable.

//IMPL
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
  requires 1 <= prices.Length <= 100000
  requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
  ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{
  max_profit := 0;
  var min_price := prices[0];
  
  var k := 1;
  while k < prices.Length
    invariant 1 <= k <= prices.Length
    invariant min_price == prices[0] || exists idx :: 0 <= idx < k && prices[idx] == min_price
    invariant forall idx :: 0 <= idx < k ==> min_price <= prices[idx]
    invariant forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
    invariant max_profit >= 0
  {
    var current_profit := prices[k] - min_price;
    if current_profit > max_profit {
      max_profit := current_profit;
    }
    if prices[k] < min_price {
      min_price := prices[k];
    }
    k := k + 1;
  }
}