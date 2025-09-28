// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max(a: i32, b: i32) -> (c: i32)
    ensures
        c >= a,
        c >= b,
        c == a || c == b,
{
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 5): added requires/ensures for price bounds to min */
fn min(a: i32, b: i32) -> (c: i32)
    requires
        0 <= a <= 10000,
        0 <= b <= 10000,
    ensures
        c <= a,
        c <= b,
        c == a || c == b,
        0 <= c <= 10000,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] >= 0 && #[trigger] prices[i] <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= #[trigger] prices[j] - #[trigger] prices[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): asserted current_price bounds to help prover */
    let mut min_price = prices[0];
    let mut max_profit = 0;
    let mut i: usize = 1;
    while i < prices.len()
        invariant
            1 <= i <= prices.len(),
            (exists|k: int| 0 <= k < i && min_price == prices[k as int]),
            (forall|k: int| 0 <= k < i ==> min_price <= prices[k as int]),
            0 <= min_price <= 10000,
            (forall|k: int, l: int| 0 <= k < l < i ==> max_profit >= prices[l as int] - prices[k as int]),
            max_profit >= 0,
        decreases prices.len() - i
    {
        let current_price = prices[i];
        assert(0 <= current_price <= 10000);
        max_profit = max(max_profit, current_price - min_price);
        min_price = min(min_price, current_price);
        i = i + 1;
    }
    max_profit
}
// </vc-code>

}
fn main() {}