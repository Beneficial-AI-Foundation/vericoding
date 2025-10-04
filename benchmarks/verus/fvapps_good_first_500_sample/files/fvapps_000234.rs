// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_descending(prices: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[i] >= prices[j]
}

spec fn is_ascending(prices: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[i] <= prices[j]
}

spec fn is_constant(prices: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < prices.len() && 0 <= j < prices.len() ==> prices[i] == prices[j]
}

fn max_profit(prices: Vec<u32>) -> (result: u32)
    ensures 
        result >= 0,
        prices.len() == 0 ==> result == 0,
        prices.len() > 0 && is_descending(prices@) ==> result == 0,
        prices.len() > 0 && is_constant(prices@) ==> result == 0,
        prices.len() >= 4 && is_ascending(prices@) ==> 
            result <= (prices[prices.len() - 1] - prices[0]) + (prices[prices.len() - 2] - prices[1]),
        prices.len() >= 2 && prices.len() < 4 && is_ascending(prices@) ==> 
            result == prices[prices.len() - 1] - prices[0]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // println!("{}", max_profit(vec![3, 3, 5, 0, 0, 3, 1, 4])); // Expected: 6
    // println!("{}", max_profit(vec![1, 2, 3, 4, 5]));          // Expected: 4  
    // println!("{}", max_profit(vec![7, 6, 4, 3, 1]));          // Expected: 0
}