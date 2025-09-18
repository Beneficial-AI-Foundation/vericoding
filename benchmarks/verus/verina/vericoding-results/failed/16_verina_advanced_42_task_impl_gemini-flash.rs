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
/* code modified by LLM (iteration 5): Fixed type issues in the initial condition by casting prices.len() to usize, consistent with the loop variable i. */
{
    if prices.len() == (0 as usize) {
        return 0;
    }

    let mut min_price: usize = prices@[0];
    let mut max_profit: usize = 0;
    let mut i: usize = 1;

    while i < prices.len() as usize
        invariant
            0 <= i,
            i <= prices.len() as usize,
            0 <= min_price,
            0 <= max_profit,
            
        decreases prices.len() - i as nat
    {
        if prices@[i] < min_price {
            min_price = prices@[i];
        } else if prices@[i] - min_price > max_profit {
            max_profit = prices@[i] - min_price;
        }
        i = i + 1;
    }

    max_profit
}
// </vc-code>

}
fn main() {}