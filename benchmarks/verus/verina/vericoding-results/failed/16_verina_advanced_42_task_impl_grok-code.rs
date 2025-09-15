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
{
    if prices.len() == 0 {
        0
    } else {
        let mut min_price = prices@[0];
        let mut max_p = 0;
        let mut i: int = 1;
        while i < prices.len()
            invariant
                i <= prices.len() &&
                decreases prices.len() - i
        {
            if prices@[i] < min_price {
                min_price = prices@[i];
            } else {
                let diff = prices@[i] - min_price;
                if diff > max_p {
                    max_p = diff;
                }
            }
            i += 1;
        }
        max_p
    }
}
// </vc-code>

}
fn main() {}