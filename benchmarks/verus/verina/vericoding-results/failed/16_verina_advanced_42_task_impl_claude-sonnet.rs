// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function for sequence indexing with proper type conversion */
fn get_price(prices: Seq<usize>, i: int) -> usize
    requires 0 <= i < prices.len()
{
    prices[i]
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
    /* code modified by LLM (iteration 5): fix type errors by using usize for indices and helper function for sequence access */
    if prices.len() == 0 {
        return 0;
    }
    
    let mut max_profit = 0;
    let mut min_price = get_price(prices, 0);
    let mut i: usize = 1;
    
    while i < prices.len()
        invariant
            0 < i <= prices.len(),
            forall|k: int| 0 <= k < i ==> min_price <= get_price(prices, k),
            (max_profit == 0) || (exists|buy: int, sell: int| 0 <= buy < sell < i && get_price(prices, sell) >= get_price(prices, buy) && get_price(prices, sell) - get_price(prices, buy) == max_profit),
    {
        let current_profit = get_price(prices, i as int) - min_price;
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        if get_price(prices, i as int) < min_price {
            min_price = get_price(prices, i as int);
        }
        i += 1;
    }
    
    max_profit
}
// </vc-code>

}
fn main() {}