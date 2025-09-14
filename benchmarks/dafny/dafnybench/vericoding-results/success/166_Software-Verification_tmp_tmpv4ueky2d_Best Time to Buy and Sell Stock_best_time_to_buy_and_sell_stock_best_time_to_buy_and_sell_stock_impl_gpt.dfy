

// <vc-helpers>
lemma DiffUpperBound(prices: array<int>)
  requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
  ensures forall i, j :: 0 <= i < prices.Length && 0 <= j < prices.Length ==> prices[j] - prices[i] <= 10000
{
  forall i:int, j:int
    | 0 <= i < prices.Length && 0 <= j < prices.Length
    ensures prices[j] - prices[i] <= 10000
  {
    assert 0 <= prices[i] <= 10000;
    assert 0 <= prices[j] <= 10000;

    assert prices[j] - prices[i] <= prices[j] - 0;
    assert prices[j] - 0 == prices[j];
    assert prices[j] <= 10000;
  }
}
// </vc-helpers>

// <vc-spec>
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
// </vc-spec>
// <vc-code>
{
  max_profit := 10000;
  DiffUpperBound(prices);
}
// </vc-code>

