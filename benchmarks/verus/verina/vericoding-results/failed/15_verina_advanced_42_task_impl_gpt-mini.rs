// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive spec helper using nat index and casting to int for Seq.index */
spec fn max_profit_rec(prices: Seq<usize>, idx: nat, min_price: usize) -> (usize)
    requires
        idx <= prices.len(),
    decreases
        prices.len() - idx
{
    if idx == prices.len() {
        0usize
    } else {
        let price = prices.index(idx as int);
        let profit_here: usize = if price > min_price { price - min_price } else { 0usize };
        let new_min = if price < min_price { price } else { min_price };
        let rest = max_profit_rec(prices, idx + 1, new_min);
        if profit_here > rest { profit_here } else { rest }
    }
}
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
/* code modified by LLM (iteration 5): call spec helper and handle empty sequence using nat zero */
    if prices.is_empty() {
        0usize
    } else {
        let zero: nat = 0;
        let first = prices.index(zero as int);
        max_profit_rec(prices, zero, first)
    }
}
// </vc-code>

}
fn main() {}