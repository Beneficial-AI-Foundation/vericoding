

// <vc-helpers>
lemma MaxProfitProperty(prices: array<int>, min_price: int, max_profit: int, k: int)
    requires 0 <= k <= prices.Length
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    requires forall i :: 0 <= i < k ==> min_price <= prices[i]
    requires forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
    ensures forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
{
}

lemma ExtendMaxProfit(prices: array<int>, min_price: int, max_profit: int, k: int)
    requires 0 <= k < prices.Length
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    requires forall i :: 0 <= i < k ==> min_price <= prices[i]
    requires forall i, j :: 0 <= i < j < k ==> max_profit >= prices[j] - prices[i]
    requires min_price <= prices[k]
    requires max_profit >= prices[k] - min_price
    ensures forall i, j :: 0 <= i < j <= k ==> max_profit >= prices[j] - prices[i]
{
    forall i, j | 0 <= i < j <= k
        ensures max_profit >= prices[j] - prices[i]
    {
        if j < k {
            assert max_profit >= prices[j] - prices[i];
        } else {
            assert j == k;
            assert min_price <= prices[i];
            assert max_profit >= prices[k] - min_price;
            assert prices[k] - min_price >= prices[k] - prices[i];
        }
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
    if prices.Length == 1 {
        return 0;
    }
    
    var min_price := prices[0];
    max_profit := 0;
    var i := 1;
    
    while i < prices.Length
        invariant 1 <= i <= prices.Length
        invariant forall k :: 0 <= k < i ==> min_price <= prices[k]
        invariant forall j, k :: 0 <= j < k < i ==> max_profit >= prices[k] - prices[j]
        invariant max_profit >= 0
    {
        if prices[i] < min_price {
            min_price := prices[i];
        }
        
        var current_profit := prices[i] - min_price;
        if current_profit > max_profit {
            max_profit := current_profit;
        }
        
        ExtendMaxProfit(prices, min_price, max_profit, i);
        i := i + 1;
    }
}
// </vc-code>

