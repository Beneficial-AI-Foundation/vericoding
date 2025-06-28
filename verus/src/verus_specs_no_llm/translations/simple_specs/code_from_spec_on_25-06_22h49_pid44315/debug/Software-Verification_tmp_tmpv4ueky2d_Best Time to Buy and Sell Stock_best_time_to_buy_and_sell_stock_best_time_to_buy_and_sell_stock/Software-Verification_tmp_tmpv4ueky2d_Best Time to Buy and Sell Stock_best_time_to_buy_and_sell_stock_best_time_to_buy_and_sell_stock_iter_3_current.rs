use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max_profit_up_to(prices: Vec<int>, end: int) -> int
    recommends 0 <= end <= prices.len()
    decreases end
{
    if end <= 1 {
        0
    } else {
        let max_from_rest = max_profit_up_to(prices, end - 1);
        let max_ending_here = max_profit_ending_at(prices, end - 1);
        if max_ending_here > max_from_rest { max_ending_here } else { max_from_rest }
    }
}

spec fn max_profit_ending_at(prices: Vec<int>, sell_day: int) -> int
    recommends 0 < sell_day < prices.len()
{
    let mut max_profit = 0;
    let mut buy_day = 0;
    while buy_day < sell_day
        invariant 0 <= buy_day <= sell_day
        decreases sell_day - buy_day
    {
        let profit = prices.spec_index(sell_day) - prices.spec_index(buy_day);
        if profit > max_profit {
            max_profit = profit;
        }
        buy_day = buy_day + 1;
    }
    max_profit
}

spec fn min_price_up_to(prices: Vec<int>, end: int) -> int
    recommends 0 < end <= prices.len()
    decreases end
{
    if end == 1 {
        prices.spec_index(0)
    } else {
        let prev_min = min_price_up_to(prices, end - 1);
        let current = prices.spec_index(end - 1);
        if current < prev_min { current } else { prev_min }
    }
}

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires
        1 <= prices.len() <= 100000,
        forall i :: 0 <= i < prices.len() ==> 0 <= prices.spec_index(i) <= 10000
    ensures
        max_profit >= 0,
        (max_profit == 0) || (exists i, j :: 0 <= i < j < prices.len() && max_profit == prices.spec_index(j) - prices.spec_index(i)),
        forall i, j :: 0 <= i < j < prices.len() ==> max_profit >= prices.spec_index(j) - prices.spec_index(i)
{
    let mut min_price = prices[0];
    let mut max_profit = 0;
    let mut k = 1;
    
    while k < prices.len()
        invariant
            1 <= k <= prices.len(),
            0 <= min_price <= 10000,
            max_profit >= 0,
            min_price == min_price_up_to(prices, k),
            forall i, j :: 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i),
            (max_profit == 0) || (exists i, j :: 0 <= i < j < k && max_profit == prices.spec_index(j) - prices.spec_index(i))
    {
        let current_price = prices[k];
        let current_profit = current_price - min_price;
        
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        
        if current_price < min_price {
            min_price = current_price;
        }
        
        k += 1;
    }
    
    max_profit
}

}