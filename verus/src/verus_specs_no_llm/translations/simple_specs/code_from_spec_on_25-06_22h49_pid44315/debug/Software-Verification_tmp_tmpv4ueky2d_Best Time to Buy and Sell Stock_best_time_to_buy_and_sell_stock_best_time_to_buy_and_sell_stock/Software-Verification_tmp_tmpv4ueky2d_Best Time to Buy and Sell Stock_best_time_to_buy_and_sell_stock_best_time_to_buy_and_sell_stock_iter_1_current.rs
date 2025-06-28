// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires
        1 <= prices.len() <= 100000,
        forall i :: 0 <= i < prices.len() ==> 0 <= prices.spec_index(i) <= 10000
    ensures
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
            forall i :: 0 <= i < k ==> min_price <= prices.spec_index(i),
            forall i, j :: 0 <= i < j < k ==> max_profit >= prices.spec_index(j) - prices.spec_index(i)
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