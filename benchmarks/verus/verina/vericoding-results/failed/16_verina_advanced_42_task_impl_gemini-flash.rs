// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `Seq::new` argument to `prices.len() as int`. */
spec fn max_profit_recursive(prices: Seq<int>, current_idx: int) -> int
    recommends
        0 <= current_idx <= prices.len(),
    ensures
        current_idx == prices.len() ==> max_profit_recursive(prices, current_idx) == 0,
        (current_idx < prices.len() && max_profit_recursive(prices, current_idx) >= 0) || current_idx == prices.len(),
        (forall|i: int, j: int| current_idx <= i < j < prices.len() ==> prices[j] < prices[i]) ==> max_profit_recursive(prices, current_idx) == 0 || (prices.len() <= 1 && max_profit_recursive(prices, current_idx) == 0),
        (exists|i: int, j: int| current_idx <= i < j < prices.len() && prices[j] >= prices[i] && prices[j] - prices[i] == max_profit_recursive(prices, current_idx)) ||
        (current_idx == prices.len() || forall|i: int, j: int| current_idx <= i < j < prices.len() ==> prices[j] < prices[i]),
    decreases prices.len() - current_idx,
{
    if current_idx == prices.len() {
        0
    } else if current_idx == prices.len() - 1 {
        0
    } else {
        let profit_if_buy_today = max_diff_for_idx(prices, current_idx);
        let profit_if_dont_buy_today = max_profit_recursive(prices, current_idx + 1);
        if profit_if_buy_today > profit_if_dont_buy_today {
            profit_if_buy_today
        } else {
            profit_if_dont_buy_today
        }
    }
}
spec fn max_diff_for_idx(prices: Seq<int>, idx: int) -> int
    recommends
        0 <= idx < prices.len(),
    ensures
        (prices.len() <= 1 && max_diff_for_idx(prices, idx) == 0) ||
        (exists|j: int| idx < j < prices.len() && prices[j] - prices[idx] == max_diff_for_idx(prices, idx)) ||
        (forall|j: int| idx < j < prices.len() ==> prices[j] < prices[idx]),
{
    if prices.len() <= 1 || idx as int >= prices.len() - 1 {
        0
    } else {
        let mut max_val: int = 0;
        let mut k = idx + 1;
        while k < prices.len()
            invariant
                idx < k <= prices.len(),
                max_val >= 0,
                forall|j: int| (idx < j < k ==> max_val >= (prices[j] - prices[idx])),
                (k == idx + 1 && max_val == 0) || (k > idx + 1 && exists|j: int| idx < j < k && max_val == prices[j] - prices[idx]),
        {
            let diff = prices[k] - prices[idx];
            if diff > max_val {
                max_val = diff;
            }
            k = k + 1;
        }
        max_val
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
/* code modified by LLM (iteration 5): Fixed type issue by casting `prices.len()` to `int` in `Seq::new` and using `@` for sequence indexing. */
{
    if prices.len() == 0 {
        0
    } else {
        let prices_int: Seq<int> = Seq::new(prices.len() as int, |i| prices@[i] as int);
        max_profit_recursive(prices_int, 0) as usize
    }
}
// </vc-code>

}
fn main() {}