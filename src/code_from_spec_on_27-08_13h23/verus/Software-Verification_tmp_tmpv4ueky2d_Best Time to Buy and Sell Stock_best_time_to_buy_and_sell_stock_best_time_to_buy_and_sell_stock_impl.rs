use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to find the minimum price up to a certain index
ghost fn min_price_up_to(prices: Seq<i32>, idx: int) -> i32
    requires 
        0 <= idx < prices.len(),
    ensures
        forall |k: int| 0 <= k <= idx ==> min_price_up_to(prices, idx) <= prices[k],
        exists |k: int| 0 <= k <= idx && min_price_up_to(prices, idx) == prices[k],
{
    if idx == 0 {
        prices[0]
    } else {
        let min_so_far = min_price_up_to(prices, idx - 1);
        if prices[idx] < min_so_far {
            prices[idx]
        } else {
            min_so_far
        }
    }
}

// Helper lemma to prove properties of min_price_up_to
proof fn lemma_min_price_up_to_monotonic(prices: Seq<i32>, idx1: int, idx2: int)
    requires 
        0 <= idx1 <= idx2 < prices.len(),
    ensures
        min_price_up_to(prices, idx1) >= min_price_up_to(prices, idx2),
{
    if idx1 == idx2 {
        return;
    }
    lemma_min_price_up_to_monotonic(prices, idx1, idx2 - 1);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] >= 0 && #[trigger] prices[i] <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= #[trigger] prices[j] - #[trigger] prices[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn best_time_to_buy_and_sell_stock(prices: &[i32]) -> (max_profit: i32)
    requires 
        1 <= prices.len() <= 100000,
        forall|i: int| 0 <= i < prices.len() ==> #[trigger] prices[i] >= 0 && #[trigger] prices[i] <= 10000,
    ensures 
        forall|i: int, j: int| 0 <= i < j < prices.len() ==> max_profit >= #[trigger] prices[j] - #[trigger] prices[i],
{
    let mut max_profit = 0;
    let mut min_price = prices[0];
    let mut i = 1;

    while i < prices.len()
        invariant
            0 <= i <= prices.len(),
            min_price <= 10000,
            min_price >= 0,
            forall |k: int| 0 <= k < i ==> min_price <= prices[k],
            forall |m: int, n: int| 0 <= m < n < i ==> max_profit >= prices[n] - prices[m],
    {
        if prices[i] < min_price {
            min_price = prices[i];
        } else {
            let current_profit = prices[i] - min_price;
            if current_profit > max_profit {
                max_profit = current_profit;
            }
        }
        i = i + 1;
    }
    max_profit
}
// </vc-code>

fn main() {}

}