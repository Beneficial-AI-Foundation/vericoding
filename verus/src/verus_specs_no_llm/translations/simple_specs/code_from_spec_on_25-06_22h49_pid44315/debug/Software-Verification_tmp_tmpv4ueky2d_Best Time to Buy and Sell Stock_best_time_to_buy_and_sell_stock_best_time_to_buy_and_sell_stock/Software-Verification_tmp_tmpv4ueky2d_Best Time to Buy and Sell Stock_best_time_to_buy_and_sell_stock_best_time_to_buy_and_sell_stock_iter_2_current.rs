use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max_profit_up_to(prices: Vec<int>, end: int) -> int
    recommends 0 <= end <= prices.len()
{
    if end <= 1 {
        0
    } else {
        let mut max_so_far = 0;
        let mut i = 0;
        while i < end {
            let mut j = i + 1;
            while j < end {
                if prices.spec_index(j) - prices.spec_index(i) > max_so_far {
                    max_so_far = prices.spec_index(j) - prices.spec_index(i);
                }
                j = j + 1;
            }
            i = i + 1;
        }
        max_so_far
    }
}

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires
        1 <= prices.len() <= 100000,
        forall i :: 0 <= i < prices.len() ==> 0 <= prices.spec_index(i) <= 10000
    ensures
        max_profit >= 0,
        exists i, j :: 0 <= i < j < prices.len() ==> max_profit == prices.spec_index(j) - prices.spec_index(i) || max_profit == 0,
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
            min_price == ({
                let mut min_so_far = prices.spec_index(0);
                let mut i = 1;
                while i < k {
                    if prices.spec_index(i) < min_so_far {
                        min_so_far = prices.spec_index(i);
                    }
                    i = i + 1;
                }
                min_so_far
            }),
            forall i, j :: 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i),
            exists i, j :: 0 <= i < j < k ==> max_profit == prices.spec_index(j) - prices.spec_index(i) || max_profit == 0
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