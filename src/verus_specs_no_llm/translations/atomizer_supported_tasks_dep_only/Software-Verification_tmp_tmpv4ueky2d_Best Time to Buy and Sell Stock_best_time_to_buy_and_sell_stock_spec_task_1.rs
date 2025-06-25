// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn best_time_to_buy_and_sell_stock(prices: Vec<int>) -> (max_profit: int)
    requires 1 <= prices.len() <= 100000,
             forall|i: int| 0 <= i < prices.len() ==> 0 <= prices[i] <= 10000
    ensures forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= prices[j] - prices[i]
{
}

}