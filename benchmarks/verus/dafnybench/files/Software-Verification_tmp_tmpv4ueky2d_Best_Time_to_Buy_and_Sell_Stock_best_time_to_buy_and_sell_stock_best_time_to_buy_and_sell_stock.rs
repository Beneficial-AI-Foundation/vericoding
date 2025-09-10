use vstd::prelude::*;

verus! {

fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] >= 0 && #[trigger] prices[i] <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= #[trigger] prices[j] - #[trigger] prices[i],
{
    assume(false);
    unreached()
}

}
fn main() {}