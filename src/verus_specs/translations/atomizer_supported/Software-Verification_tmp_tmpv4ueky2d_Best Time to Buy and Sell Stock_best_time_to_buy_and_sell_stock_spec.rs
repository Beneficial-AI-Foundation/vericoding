pub fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires(1 <= prices.len() <= 100000)
    requires(forall|i: int| 0 <= i < prices.len() ==> 0 <= prices[i] <= 10000)
    ensures(|max_profit: i32| forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices[j] - prices[i])
{
}