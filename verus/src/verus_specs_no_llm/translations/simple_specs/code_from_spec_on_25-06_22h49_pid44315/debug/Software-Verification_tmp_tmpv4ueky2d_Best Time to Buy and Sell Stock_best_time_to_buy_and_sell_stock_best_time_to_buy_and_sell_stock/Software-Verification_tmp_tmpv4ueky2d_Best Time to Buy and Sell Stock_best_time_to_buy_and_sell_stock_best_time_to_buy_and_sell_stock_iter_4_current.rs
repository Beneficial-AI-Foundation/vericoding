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
    decreases sell_day
{
    max_profit_ending_at_helper(prices, sell_day, 0)
}

spec fn max_profit_ending_at_helper(prices: Vec<int>, sell_day: int, buy_day: int) -> int
    recommends 0 <= buy_day <= sell_day < prices.len()
    decreases sell_day - buy_day
{
    if buy_day >= sell_day {
        0
    } else {
        let profit = prices.spec_index(sell_day) - prices.spec_index(buy_day);
        let rest_profit = max_profit_ending_at_helper(prices, sell_day, buy_day + 1);
        if profit > rest_profit { profit } else { rest_profit }
    }
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

proof fn lemma_min_price_up_to_properties(prices: Vec<int>, end: int)
    requires 0 < end <= prices.len()
    ensures 
        exists i :: 0 <= i < end && min_price_up_to(prices, end) == prices.spec_index(i),
        forall i :: 0 <= i < end ==> min_price_up_to(prices, end) <= prices.spec_index(i)
    decreases end
{
    if end == 1 {
        // Base case is trivial
    } else {
        lemma_min_price_up_to_properties(prices, end - 1);
    }
}

proof fn lemma_max_profit_properties(prices: Vec<int>, k: int)
    requires 1 <= k <= prices.len()
    ensures forall i, j :: 0 <= i < j < k ==> prices.spec_index(j) - min_price_up_to(prices, j) >= prices.spec_index(j) - prices.spec_index(i)
{
    // This lemma helps prove that using min_price gives optimal profit
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
    
    proof {
        lemma_min_price_up_to_properties(prices, 1);
    }
    
    while k < prices.len()
        invariant
            1 <= k <= prices.len(),
            0 <= min_price <= 10000,
            max_profit >= 0,
            min_price == min_price_up_to(prices, k),
            forall i, j :: 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i),
            (max_profit == 0) || (exists i, j :: 0 <= i < j < k && max_profit == prices.spec_index(j) - prices.spec_index(i)),
            exists idx :: 0 <= idx < k && min_price == prices.spec_index(idx),
            forall i :: 0 <= i < k ==> min_price <= prices.spec_index(i)
    {
        let current_price = prices[k];
        let current_profit = current_price - min_price;
        
        proof {
            lemma_min_price_up_to_properties(prices, k + 1);
            lemma_max_profit_properties(prices, k);
        }
        
        if current_profit > max_profit {
            max_profit = current_profit;
            
            proof {
                // We need to show that there exist indices for the new max_profit
                assert(exists idx :: 0 <= idx < k && min_price == prices.spec_index(idx));
            }
        }
        
        if current_price < min_price {
            min_price = current_price;
        }
        
        k += 1;
    }
    
    max_profit
}

}