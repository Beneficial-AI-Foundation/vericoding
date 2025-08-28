use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max_profit_spec(prices: Seq<i32>) -> i32 {
    max_profit_between_days(prices, 0, prices.len())
}

spec fn max_profit_between_days(prices: Seq<i32>, start: int, end: int) -> i32 
    decreases end - start
{
    if start >= end || end - start <= 1 {
        0
    } else {
        let profit_excluding_first = max_profit_between_days(prices, start + 1, end);
        let max_profit_with_first_as_buy = max_profit_with_buy_day(prices, start, start + 1, end);
        if profit_excluding_first >= max_profit_with_first_as_buy {
            profit_excluding_first
        } else {
            max_profit_with_first_as_buy
        }
    }
}

spec fn max_profit_with_buy_day(prices: Seq<i32>, buy_day: int, sell_start: int, sell_end: int) -> i32
    decreases sell_end - sell_start
{
    if sell_start >= sell_end {
        0
    } else {
        let current_profit = prices[sell_start] - prices[buy_day];
        let rest_profit = max_profit_with_buy_day(prices, buy_day, sell_start + 1, sell_end);
        if current_profit >= rest_profit {
            current_profit
        } else {
            rest_profit
        }
    }
}

proof fn lemma_max_profit_bound(prices: Seq<i32>, buy_day: int, sell_day: int)
    requires
        0 <= buy_day < sell_day < prices.len(),
        forall|i: int| 0 <= i < prices.len() ==> prices[i] >= 0 && prices[i] <= 10000,
    ensures
        prices[sell_day] - prices[buy_day] <= max_profit_spec(prices)
{
    lemma_max_profit_between_days_bound(prices, 0, prices.len(), buy_day, sell_day);
}

proof fn lemma_max_profit_between_days_bound(prices: Seq<i32>, start: int, end: int, buy_day: int, sell_day: int)
    requires
        0 <= start <= buy_day < sell_day < end <= prices.len(),
        forall|i: int| 0 <= i < prices.len() ==> prices[i] >= 0 && prices[i] <= 10000,
    ensures
        prices[sell_day] - prices[buy_day] <= max_profit_between_days(prices, start, end)
    decreases end - start
{
    if start >= end || end - start <= 1 {
    } else if buy_day == start {
        lemma_max_profit_with_buy_day_bound(prices, buy_day, start + 1, end, sell_day);
    } else {
        lemma_max_profit_between_days_bound(prices, start + 1, end, buy_day, sell_day);
    }
}

proof fn lemma_max_profit_with_buy_day_bound(prices: Seq<i32>, buy_day: int, sell_start: int, sell_end: int, sell_day: int)
    requires
        0 <= buy_day < prices.len(),
        sell_start <= sell_day < sell_end <= prices.len(),
        forall|i: int| 0 <= i < prices.len() ==> prices[i] >= 0 && prices[i] <= 10000,
    ensures
        prices[sell_day] - prices[buy_day] <= max_profit_with_buy_day(prices, buy_day, sell_start, sell_end)
    decreases sell_end - sell_start
{
    if sell_start >= sell_end {
    } else if sell_day == sell_start {
    } else {
        lemma_max_profit_with_buy_day_bound(prices, buy_day, sell_start + 1, sell_end, sell_day);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] >= 0 && #[trigger] prices[i] <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= #[trigger] prices[j] - #[trigger] prices[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut max_profit = 0i32;
    let mut min_price = prices[0];
    let mut i = 1;
    
    while i < prices.len()
        invariant
            1 <= i <= prices.len(),
            min_price >= 0,
            max_profit >= 0,
            forall|buy: int, sell: int| 0 <= buy < sell < i ==> max_profit >= prices@[sell] - prices@[buy],
            exists|k: int| 0 <= k < i && min_price == prices@[k],
            forall|k: int| 0 <= k < i ==> min_price <= prices@[k],
    {
        let current_profit = prices[i] - min_price;
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        if prices[i] < min_price {
            min_price = prices[i];
        }
        i = i + 1;
    }
    
    max_profit
}
// </vc-code>

fn main() {}

}