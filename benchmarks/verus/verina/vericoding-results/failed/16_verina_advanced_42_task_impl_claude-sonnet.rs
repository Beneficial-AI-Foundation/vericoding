// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed spec functions with imperative code */
spec fn has_profitable_pair(prices: Seq<usize>) -> bool {
    exists|i: int, j: int| 0 <= i < j < prices.len() && prices[j] >= prices[i]
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
/* code modified by LLM (iteration 5): fixed nat literal syntax */
{
    if prices.len() == 0 {
        return 0;
    }
    
    let mut max_profit = 0;
    let mut i = 0;
    
    while i < prices.len()
        invariant 0 <= i <= prices.len()
    {
        let mut j = i + 1;
        while j < prices.len()
            invariant i < j <= prices.len()
        {
            if prices[j] >= prices[i] {
                let profit = prices[j] - prices[i];
                if profit > max_profit {
                    max_profit = profit;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    max_profit
}
// </vc-code>

}
fn main() {}