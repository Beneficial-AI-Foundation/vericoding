// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions are needed for this problem. */
// </vc-helpers>

// <vc-spec>
fn max_profit(prices: Seq<usize>) -> (result: usize)
    ensures
        (result == 0 && prices.len() == 0) ||
        (exists|i: int, j: int| 0 <= i < j < prices.len() && prices[j] >= prices[i] && prices[j] - prices[i] == result) ||
        (forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[j] < prices[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Addressed the type issue when indexing `prices` by using `prices[i]` directly which is valid for `usize` indices. Updated the loop invariant to correctly track `min_price_so_far` against prices seen and ensure `max_p` represents the maximum profit found so far. */
{
    let n = prices.len();
    if n == 0 {
        return 0;
    }

    let mut max_p: usize = 0;
    let mut min_price_so_far: usize = prices[0];

    let mut i: usize = 1;
    while i < n
        invariant
            0 < i,
            i <= n,
            max_p >= 0,
            min_price_so_far >= 0,
            min_price_so_far == prices.subsequence(0, i as int).fold(prices[0], |a, b| if a < b { a } else { b }),
            (forall|x: int, y: int|
                0 <= x < y < i as int
                ==>
                max_p as int >= prices[y] as int - prices[x] as int
            ),
            (exists|x: int, y: int| 0 <= x < y && y < i && prices[y] >= prices[x] && max_p == prices[y] - prices[x]) ||
            (forall|x: int, y: int| 0 <= x < y && y < i ==> prices[y] < prices[x]) ||
            max_p == 0,

    {
        let current_price = prices[i];
        if current_price < min_price_so_far {
            min_price_so_far = current_price;
        } else if current_price - min_price_so_far > max_p {
            max_p = current_price - min_price_so_far;
        }
        i = i + 1;
    }
    max_p
}
// </vc-code>

}
fn main() {}