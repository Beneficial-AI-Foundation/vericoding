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
        assert(min_price_up_to(prices, 1) == prices.spec_index(0));
        assert(exists|i: int| 0 <= i < 1 && min_price_up_to(prices, 1) == prices.spec_index(i));
        assert(forall|i: int| 0 <= i < 1 ==> min_price_up_to(prices, 1) <= prices.spec_index(i));
    } else {
        lemma_min_price_up_to_properties(prices, end - 1);
        let prev_min = min_price_up_to(prices, end - 1);
        let current = prices.spec_index(end - 1);
        
        if current < prev_min {
            assert(min_price_up_to(prices, end) == current);
            assert(current == prices.spec_index(end - 1));
            assert(exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices.spec_index(i));
            // Prove the forall property
            assert(forall|i: int| 0 <= i < end - 1 ==> prev_min <= prices.spec_index(i));
            assert(current < prev_min);
            assert(forall|i: int| 0 <= i < end ==> current <= prices.spec_index(i));
        } else {
            assert(min_price_up_to(prices, end) == prev_min);
            assert(exists|i: int| 0 <= i < end - 1 && prev_min == prices.spec_index(i));
            assert(exists|i: int| 0 <= i < end && min_price_up_to(prices, end) == prices.spec_index(i));
            assert(forall|i: int| 0 <= i < end - 1 ==> prev_min <= prices.spec_index(i));
            assert(prev_min <= current);
            assert(forall|i: int| 0 <= i < end ==> prev_min <= prices.spec_index(i));
        }
    }
}

proof fn lemma_max_profit_properties(prices: Vec<int>, k: int)
    requires 1 <= k <= prices.len()
    ensures forall|i: int, j: int| 0 <= i < j < k ==> prices.spec_index(j) - min_price_up_to(prices, j + 1) >= prices.spec_index(j) - prices.spec_index(i)
{
    if k > 1 {
        let j = k - 1;
        if j > 0 {
            lemma_min_price_up_to_properties(prices, j + 1);
            assert(forall|i: int| 0 <= i < j + 1 ==> min_price_up_to(prices, j + 1) <= prices.spec_index(i));
            assert(forall|i: int| 0 <= i < j ==> min_price_up_to(prices, j + 1) <= prices.spec_index(i));
            assert(forall|i: int| 0 <= i < j ==> prices.spec_index(j) - min_price_up_to(prices, j + 1) >= prices.spec_index(j) - prices.spec_index(i));
        }
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
    
    proof {
        lemma_min_price_up_to_properties(prices, 1);
        assert(min_price == prices.spec_index(0));
        assert(min_price_up_to(prices, 1) == prices.spec_index(0));
    }
    
    while k < prices.len()
        invariant
            1 <= k <= prices.len(),
            0 <= min_price <= 10000,
            max_profit >= 0,
            min_price == min_price_up_to(prices, k),
            forall|i: int, j: int| 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i),
            (max_profit == 0) || (exists|i: int, j: int| 0 <= i < j < k && max_profit == prices.spec_index(j) - prices.spec_index(i)),
            exists|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx),
            forall|i: int| 0 <= i < k ==> min_price <= prices.spec_index(i)
    {
        let current_price = prices[k];
        let current_profit = current_price - min_price;
        
        proof {
            if k + 1 <= prices.len() {
                lemma_min_price_up_to_properties(prices, k + 1);
            }
            lemma_max_profit_properties(prices, k + 1);
            
            // Prove that current_profit represents a valid transaction
            assert(exists|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx));
            let buy_idx = choose|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx);
            assert(current_profit == prices.spec_index(k) - prices.spec_index(buy_idx));
            assert(0 <= buy_idx < k);
            assert(buy_idx < k < k + 1);
        }
        
        let old_max_profit = max_profit;
        if current_profit > max_profit {
            max_profit = current_profit;
            proof {
                let buy_idx = choose|idx: int| 0 <= idx < k && min_price == prices.spec_index(idx);
                assert(max_profit == prices.spec_index(k) - prices.spec_index(buy_idx));
                assert(0 <= buy_idx < k < k + 1);
                assert(exists|i: int, j: int| 0 <= i < j < k + 1 && max_profit == prices.spec_index(j) - prices.spec_index(i));
            }
        }
        
        let old_min = min_price;
        if current_price < min_price {
            min_price = current_price;
        }
        
        proof {
            // Prove min_price invariant for next iteration
            if current_price < old_min {
                assert(min_price == current_price);
                assert(current_price == prices.spec_index(k));
                assert(min_price_up_to(prices, k + 1) == current_price);
                assert(min_price == min_price_up_to(prices, k + 1));
            } else {
                assert(min_price == old_min);
                assert(old_min == min_price_up_to(prices, k));
                assert(min_price_up_to(prices, k + 1) == old_min);
                assert(min_price == min_price_up_to(prices, k + 1));
            }
            
            // Prove max_profit maintains optimality
            assert(forall|i: int, j: int| 0 <= i < j < k ==> old_max_profit >= prices.spec_index(j) - prices.spec_index(i));
            assert(forall|i: int, j: int| 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i));
            
            // Prove for the new element k
            assert(forall|i: int| 0 <= i < k ==> min_price <= prices.spec_index(i));
            assert(forall|i: int| 0 <= i < k ==> max_profit >= prices.spec_index(k) - prices.spec_index(i));
            assert(forall|i: int, j: int| 0 <= i < j < k + 1 ==> max_profit >= prices.spec_index(j) - prices.spec_index(i));
        }
        
        k = k + 1;
    }
    
    proof {
        assert(k == prices.len());
        assert(forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices.spec_index(j) - prices.spec_index(i));
    }
    
    max_profit
}

}