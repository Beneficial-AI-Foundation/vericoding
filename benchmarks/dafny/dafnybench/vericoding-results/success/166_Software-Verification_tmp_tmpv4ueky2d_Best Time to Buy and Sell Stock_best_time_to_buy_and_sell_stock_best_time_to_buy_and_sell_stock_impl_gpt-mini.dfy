

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
// </vc-spec>
// <vc-code>
{
  if prices.Length == 1 {
    return 0;
  }
  var n := prices.Length;
  var min_price := prices[0];
  max_profit := prices[1] - prices[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall a, b :: 0 <= a < b < i ==> max_profit >= prices[b] - prices[a]
    invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
    decreases n - i
  {
    var p := prices[i];
    if p - min_price > max_profit {
      max_profit := p - min_price;
    }
    if p < min_price {
      min_price := p;
    }
    i := i + 1;
  }
  return max_profit;
}
// </vc-code>

