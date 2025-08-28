// <vc-helpers>
// Helper lemma to ensure properties of minimum price
lemma MinPriceProperty(prices: array<int>, min_price: int, i: int)
    requires 1 <= prices.Length <= 100000
    requires 0 <= i < prices.Length
    requires forall k :: 0 <= k < prices.Length ==> 0 <= prices[k] <= 10000
    requires forall k :: 0 <= k < i ==> min_price <= prices[k]
    ensures forall k :: 0 <= k < i ==> min_price <= prices[k]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method BestTimeToBuyAndSellStock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{
    max_profit := 0;
    if prices.Length == 1 {
        return;
    }
    
    var min_price := prices[0];
    var i := 1;
    
    while i < prices.Length
        invariant 0 <= i <= prices.Length
        invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
        invariant forall k, m :: 0 <= k < m < i ==> max_profit >= prices[m] - prices[k]
    {
        if prices[i] < min_price {
            min_price := prices[i];
        }
        var current_profit := prices[i] - min_price;
        if current_profit > max_profit {
            max_profit := current_profit;
        }
        i := i + 1;
    }
}
// </vc-code>
