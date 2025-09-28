// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return types and indexing operations */
proof fn spec_min_price(prices: Seq<usize>, idx: int) -> (min_price: usize)
    requires
        0 <= idx <= prices.len(),
    ensures
        min_price == prices.index(0) || (exists|i: int| 0 <= i < idx && prices.index(i) == min_price),
        forall|i: int| 0 <= i < idx ==> min_price <= prices.index(i)
{
    if idx == 0 {
        prices.index(0)
    } else {
        let prev_min = spec_min_price(prices, idx - 1);
        if prices.index(idx - 1) < prev_min {
            prices.index(idx - 1)
        } else {
            prev_min
        }
    }
}

proof fn spec_max_profit(prices: Seq<usize>, idx: int) -> (max_profit: usize)
    requires
        0 <= idx <= prices.len(),
    ensures
        max_profit == 0 || (exists|i: int, j: int| 0 <= i < j < idx && prices.index(j) - prices.index(i) == max_profit),
        forall|i: int, j: int| 0 <= i < j < idx ==> prices.index(j) - prices.index(i) <= max_profit
{
    if idx <= 1 {
        0
    } else {
        let prev_max = spec_max_profit(prices, idx - 1);
        let current_min = spec_min_price(prices, idx - 1);
        let potential_profit = if prices.index(idx - 1) > current_min { prices.index(idx - 1) - current_min } else { 0 };
        if potential_profit > prev_max {
            potential_profit as usize
        } else {
            prev_max
        }
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
/* code modified by LLM (iteration 5): Fixed indexing syntax and type conversions */
{
    if prices.len() == 0 {
        return 0;
    }
    
    let mut max_profit: usize = 0;
    let mut min_price: usize = prices.index(0);
    
    let mut idx: usize = 1;
    while idx < prices.len() as usize
        invariant
            idx <= prices.len() as usize,
            min_price == spec_min_price(prices, idx as int),
            max_profit == spec_max_profit(prices, idx as int)
        decreases prices.len() as usize - idx
    {
        let current_price = prices.index(idx as int);
        if current_price < min_price {
            min_price = current_price;
        } else if current_price - min_price > max_profit {
            max_profit = current_price - min_price;
        }
        idx = idx + 1;
    }
    
    max_profit
}
// </vc-code>

}
fn main() {}