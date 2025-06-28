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
    prices[sell_day] - min_price_up_to(prices, sell_day)
}

spec fn min_price_up_to(prices: Vec<int>, end: int) -> int
    recommends 0 < end <= prices.len()
    decreases end
{
    if end == 1 {
        prices[0]
    } else {
        let prev_min = min_price_up_to(prices, end - 1);
        let current = prices[end - 1];
        if current < prev_min { current } else { prev_min }
    }
}

proof fn lemma_min_price_up_to_properties(prices: Vec<int>, end: int)
    requires 0 < end <= prices.len()
    ensures 
        exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices[i],
        forall|i: int| 0 <= i < end ==> min_price_up_to(prices, end) <= prices[i]
    decreases end
{
    if end == 1 {
        assert(min_price_up_to(prices, end) == prices[0]);
        assert(exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices[i]) by {
            assert(0 <= 0 < end && min_price_up_to(prices, end) == prices[0]);
        }
    } else {
        lemma_min_price_up_to_properties(prices, end - 1);
        let prev_min = min_price_up_to(prices, end - 1);
        let current = prices[end - 1];
        if current < prev_min {
            assert(min_price_up_to(prices, end) == current);
            assert(exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices[i]) by {
                assert(0 <= (end - 1) < end && min_price_up_to(prices, end) == prices[end - 1]);
            }
        } else {
            assert(min_price_up_to(prices, end) == prev_min);
        }
    }
}

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> 0 <= prices[i] <= 10000
    ensures
        max_profit >= 0,
        (max_profit == 0) || (exists|i: int, j: int| 0 <= i < j < prices.len() && max_profit == prices[j] - prices[i]),
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices[j] - prices[i]
{
    if prices.len() == 1 {
        return 0;
    }
    
    let mut min_price = prices[0];
    let mut max_profit = 0;
    let mut k = 1;
    
    // We need to track the index where min_price was found
    let mut min_price_idx = 0;
    
    while k < prices.len()
        invariant
            1 <= k <= prices.len(),
            0 <= min_price <= 10000,
            max_profit >= 0,
            0 <= min_price_idx < k,
            min_price == prices[min_price_idx],
            forall|i: int| 0 <= i < k ==> min_price <= prices[i],
            forall|i: int, j: int| 0 <= i < j < k ==> max_profit >= prices[j] - prices[i],
            (max_profit == 0) || (exists|i: int, j: int| 0 <= i < j < k && max_profit == prices[j] - prices[i])
    {
        let current_price = prices[k];
        let current_profit = current_price - min_price;
        
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        
        if current_price < min_price {
            min_price = current_price;
            min_price_idx = k;
        }
        
        k = k + 1;
    }
    
    // Final proof to establish postconditions
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices[j] - prices[i]);
        if max_profit > 0 {
            assert(exists|i: int, j: int| 0 <= i < j < prices.len() && max_profit == prices[j] - prices[i]);
        }
    }
    
    max_profit
}

}