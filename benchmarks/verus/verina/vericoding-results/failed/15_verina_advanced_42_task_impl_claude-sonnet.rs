// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed spec functions to be properly specified and removed invalid executable code in spec functions */
spec fn valid_profit_pair(prices: Seq<usize>, i: int, j: int) -> bool {
    0 <= i < j < prices.len() && prices[j] >= prices[i]
}

spec fn profit_value(prices: Seq<usize>, i: int, j: int) -> int 
    requires valid_profit_pair(prices, i, j)
{
    (prices[j] - prices[i]) as int
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
    /* code modified by LLM (iteration 5): Fixed ghost type usage by removing int casts and using direct usize indexing */
    if prices.len() == 0 {
        return 0;
    }
    
    let mut max_profit = 0;
    let mut i: usize = 0;
    
    while i < prices.len() as usize
        invariant 
            0 <= i <= prices.len(),
            max_profit >= 0
    {
        let mut j: usize = i + 1;
        while j < prices.len() as usize
            invariant
                i < j <= prices.len(),
                max_profit >= 0
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