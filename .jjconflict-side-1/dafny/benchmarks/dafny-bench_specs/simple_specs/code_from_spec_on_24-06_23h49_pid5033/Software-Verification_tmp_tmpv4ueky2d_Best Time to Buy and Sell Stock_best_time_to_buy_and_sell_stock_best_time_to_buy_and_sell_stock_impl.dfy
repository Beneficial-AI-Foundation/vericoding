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
    /* code modified by LLM (iteration 4): min_price is minimum of prices seen so far */
    invariant exists i :: 0 <= i < k && prices[i] == min_price
    invariant forall i :: 0 <= i < k ==> min_price <= prices[i]
    /* code modified by LLM (iteration 4): max_profit is at least the maximum profit from all pairs seen so far */
    invariant forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
    /* code modified by LLM (iteration 4): max_profit is at least the best profit using any earlier min_price */
    invariant forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - min_price
  {
    /* code modified by LLM (iteration 4): Calculate potential profit with current price */
    var current_profit := prices[k] - min_price;
    if current_profit > max_profit {
      max_profit := current_profit;
    }
    
    /* code modified by LLM (iteration 4): Update min_price for future iterations */
    if prices[k] < min_price {
      min_price := prices[k];
    }
  }
}