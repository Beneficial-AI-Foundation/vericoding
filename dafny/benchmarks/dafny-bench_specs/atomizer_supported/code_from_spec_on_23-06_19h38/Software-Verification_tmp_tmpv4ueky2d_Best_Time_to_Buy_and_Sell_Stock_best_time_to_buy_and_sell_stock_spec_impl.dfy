//IMPL 
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{
    max_profit := 0;
    var min_price := prices[0];
    
    /* code modified by LLM (iteration 3): Fixed loop invariants - min_price tracks minimum of all prices seen so far, and corrected profit tracking logic */
    for k := 1 to prices.Length
        invariant 0 <= max_profit
        invariant forall m :: 0 <= m < k ==> min_price <= prices[m]
        invariant forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
    {
        var current_profit := prices[k] - min_price;
        if current_profit > max_profit {
            max_profit := current_profit;
        }
        if prices[k] < min_price {
            min_price := prices[k];
        }
    }
}