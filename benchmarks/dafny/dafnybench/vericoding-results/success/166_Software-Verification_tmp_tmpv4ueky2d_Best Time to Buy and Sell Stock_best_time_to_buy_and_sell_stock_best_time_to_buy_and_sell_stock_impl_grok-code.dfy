

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
// </vc-spec>
// <vc-code>
{
  if prices.Length == 0 { return 0; }
  var min_price := prices[0];
  max_profit := 0;
  var i := 1;
  while i < prices.Length
    decreases prices.Length - i
    invariant 0 <= i <= prices.Length
    invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
    invariant forall n, m :: 0 <= n < m < i ==> max_profit >= prices[m] - prices[n]
  {
    min_price := if prices[i] < min_price then prices[i] else min_price;
    var cur := prices[i] - min_price;
    max_profit := if cur > max_profit then cur else max_profit;
    i := i + 1;
  }
  return max_profit;
}
// </vc-code>

