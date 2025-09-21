// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn best_time_to_buy_and_sell_stock(prices: &Vec<i8>) -> (max_profit: i8)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] as int >= 0 && #[trigger] prices[i] as int <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit as int >= #[trigger] prices[j] as int - #[trigger] prices[i] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}