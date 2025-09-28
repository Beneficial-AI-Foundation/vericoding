// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_profit(prices: Seq<usize>) -> (result: usize)
    ensures
        (result == 0 && prices.len() == 0) ||
        (exists|i: int, j: int| 0 <= i < j < prices.len() && prices[j] >= prices[i] && prices[j] - prices[i] == result) ||
        (forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[j] < prices[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed int to usize in executable code, as int is ghost type */
{
    if prices.len() == 0 {
        0
    } else {
        let mut min_price = prices[0];
        let mut max_profit = 0;
        let mut i: usize = 1;
        while i < prices.len()
            invariant
                i >= 1,
                i <= prices.len(),
                max_profit >= 0
            decreases prices.len() - i
        {
            let curr_price = prices[i];
            if curr_price > min_price {
                if curr_price - min_price > max_profit {
                    max_profit = curr_price - min_price;
                }
            }
            if curr_price < min_price {
                min_price = curr_price;
            }
            i = i + 1;
        }
        max_profit
    }
}
// </vc-code>

}
fn main() {}