// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
// </vc-spec>
// <vc-code>
{
  max_profit := 0;
  if prices.Length > 0 {
    var min_price := prices[0];
    var i := 1;
    while i < prices.Length
      invariant 1 <= i <= prices.Length
      invariant 0 <= max_profit
      invariant exists k :: 0 <= k < i && min_price == prices[k]
      invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
      invariant forall j, k :: 0 <= j < k < i ==> max_profit >= prices[k] - prices[j]
    {
      max_profit := max(max_profit, prices[i] - min_price);
      min_price := min(min_price, prices[i]);
      i := i + 1;
    }
  }
}
// </vc-code>
