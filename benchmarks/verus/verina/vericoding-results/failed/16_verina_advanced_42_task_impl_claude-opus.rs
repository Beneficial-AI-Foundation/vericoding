// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_profit(prices: Seq<usize>, i: int, j: int, profit: usize) -> bool {
    0 <= i < j < prices.len() && prices[j] >= prices[i] && prices[j] - prices[i] == profit
}

spec fn no_profit_exists(prices: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < prices.len() ==> prices[j] < prices[i]
}

spec fn max_profit_spec(prices: Seq<usize>) -> usize
    decreases prices.len()
{
    if prices.len() <= 1 {
        0
    } else {
        let rest_max = max_profit_spec(prices.subrange(1, prices.len() as int));
        let current_max = find_max_with_first(prices);
        if current_max > rest_max { current_max } else { rest_max }
    }
}

spec fn find_max_with_first(prices: Seq<usize>) -> usize
    recommends prices.len() >= 2
{
    if prices.len() < 2 {
        0
    } else {
        find_max_with_first_rec(prices, 1, 0)
    }
}

spec fn find_max_with_first_rec(prices: Seq<usize>, j: int, max_so_far: usize) -> usize
    recommends 0 < j <= prices.len()
    decreases prices.len() - j
{
    if j >= prices.len() {
        max_so_far
    } else {
        let profit = if prices[j] >= prices[0] { (prices[j] - prices[0]) as usize } else { 0 };
        let new_max = if profit > max_so_far { profit } else { max_so_far };
        find_max_with_first_rec(prices, j + 1, new_max)
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
    /* code modified by LLM (iteration 5): Fixed type error by using usize index directly without int cast */
    if prices.len() == 0 {
        return 0;
    }
    
    let mut max_profit_val: usize = 0;
    let mut min_price: usize = prices@[0];
    let mut i: usize = 1;
    
    while i < prices.len()
        invariant
            1 <= i <= prices.len(),
            forall|k: int| 0 <= k < i as int ==> min_price <= prices@[k] || exists|m: int| 0 <= m < i as int && prices@[m] == min_price,
            (exists|buy: int, sell: int| 0 <= buy < sell < i as int && prices@[sell] >= prices@[buy] && prices@[sell] - prices@[buy] == max_profit_val) || max_profit_val == 0,
            forall|buy: int, sell: int| 0 <= buy < sell < i as int && prices@[sell] >= prices@[buy] ==> prices@[sell] - prices@[buy] <= max_profit_val,
    {
        let current_price = prices@[i];
        if current_price >= min_price {
            let profit = current_price - min_price;
            if profit > max_profit_val {
                max_profit_val = profit;
            }
        } else {
            min_price = current_price;
        }
        i = i + 1;
    }
    
    max_profit_val
}
// </vc-code>

}
fn main() {}