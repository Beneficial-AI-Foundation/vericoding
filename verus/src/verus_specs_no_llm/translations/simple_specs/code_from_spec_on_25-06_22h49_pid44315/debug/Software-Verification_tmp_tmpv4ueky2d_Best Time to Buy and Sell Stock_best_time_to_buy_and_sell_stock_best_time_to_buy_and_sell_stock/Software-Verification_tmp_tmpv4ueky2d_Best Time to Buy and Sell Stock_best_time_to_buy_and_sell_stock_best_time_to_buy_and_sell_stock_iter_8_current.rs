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
    prices.spec_index(sell_day) - min_price_up_to(prices, sell_day)
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
        exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices.spec_index(i),
        forall|i: int| 0 <= i < end ==> min_price_up_to(prices, end) <= prices.spec_index(i)
    decreases end
{
    if end == 1 {
        // Base case is trivial
    } else {
        lemma_min_price_up_to_properties(prices, end - 1);
        // Inductive case follows from definition
    }
}

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> 0 <= prices.spec_index(i) <= 10000
    ensures
        max_profit >= 0,
        (max_profit == 0) || (exists|i: int, j: int| 0 <= i < j < prices.len() && max_profit == prices.spec_index(j) - prices.spec_index(i)),
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices.spec_index(j) - prices.spec_index(i)
{
    if prices.len() == 1 {
        return 0;
    }
    
    let mut min_price = prices[0];
    let mut max_profit = 0;
    let mut k = 1;
    
    while k < prices.len()
        invariant
            1 <= k <= prices.len(),
            0 <= min_price <= 10000,
            max_profit >= 0,
            exists|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx),
            forall|i: int| 0 <= i < k ==> min_price <= prices.spec_index(i),
            forall|i: int, j: int| 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i),
            (max_profit == 0) || (exists|i: int, j: int| 0 <= i < j < k && max_profit == prices.spec_index(j) - prices.spec_index(i))
    {
        let current_price = prices[k];
        let current_profit = current_price - min_price;
        
        proof {
            // Current profit represents a valid transaction
            let buy_idx = choose|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx);
            assert(current_profit == prices.spec_index(k) - prices.spec_index(buy_idx));
            assert(0 <= buy_idx < k);
        }
        
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        
        if current_price < min_price {
            min_price = current_price;
        }
        
        proof {
            // Maintain invariants for next iteration
            assert(exists|idx: int| 0 <= idx < k + 1 && min_price == prices.spec_index(idx));
            assert(forall|i: int| 0 <= i < k + 1 ==> min_price <= prices.spec_index(i));
            
            // Max profit optimality is maintained
            assert(forall|i: int| 0 <= i < k ==> max_profit >= prices.spec_index(k) - prices.spec_index(i));
        }
        
        k = k + 1;
    }
    
    max_profit
}

}