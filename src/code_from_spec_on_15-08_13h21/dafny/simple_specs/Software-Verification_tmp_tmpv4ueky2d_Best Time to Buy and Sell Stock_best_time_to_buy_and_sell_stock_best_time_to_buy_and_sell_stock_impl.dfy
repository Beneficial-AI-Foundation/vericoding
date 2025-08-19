//IMPL
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
  requires 1 <= prices.Length <= 100000
  requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
  ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{
  max_profit := 0;
  var min_price := prices[0];
  
  for k := 1 to prices.Length
    invariant 0 <= max_profit
    invariant min_price == prices[0] || exists idx :: 0 <= idx < k && prices[idx] == min_price
    invariant forall idx :: 0 <= idx < k ==> min_price <= prices[idx]
    invariant forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
  {
    if prices[k] - min_price > max_profit {
      max_profit := prices[k] - min_price;
    }
    if prices[k] < min_price {
      min_price := prices[k];
    }
  }
}