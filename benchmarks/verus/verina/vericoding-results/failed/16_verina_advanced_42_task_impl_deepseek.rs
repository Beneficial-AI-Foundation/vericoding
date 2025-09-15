// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed nat/int conversions and sequence indexing */
proof fn lemma_subtraction_order(a: int, b: int)
    requires a >= b
    ensures a - b >= 0
{
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

proof fn lemma_max_min_property(a: int, b: int, c: int)
    requires a <= b <= c
    ensures max(a, c) - min(a, c) >= b - a,
            max(a, c) - min(a, c) >= c - b
{
}

spec fn seq_index<T>(s: Seq<T>, idx: int) -> T
    requires 0 <= idx < s.len()
{
    s[idx]
}

spec fn usize_to_int(x: usize) -> int {
    x as int
}

proof fn lemma_preserves_value(v: usize) 
    ensures v as int == usize_to_int(v)
{
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
/* code modified by LLM (iteration 4): Fixed compilation errors with proper type handling */
{
    if prices.len() == 0 {
        return 0;
    }
    
    let mut min_price: usize = prices[0];
    let mut max_profit: usize = 0;
    
    let mut i: usize = 0;
    while i < prices.len()
        invariant
            i <= prices.len(),
            0 <= min_price,
            max_profit >= 0,
            (forall|k: int| 0 <= k < i ==> min_price <= prices.index(k)),
            (exists|l: int, m: int| 0 <= l < m < i && prices.index(m) >= prices.index(l) && prices.index(m) - prices.index(l) == max_profit) || max_profit == 0
    {
        if prices[i] < min_price {
            min_price = prices[i];
        }
        
        let current_profit = prices[i] - min_price;
        if current_profit > max_profit {
            max_profit = current_profit;
        }
        
        i += 1;
    }
    
    max_profit
}
// </vc-code>

}
fn main() {}