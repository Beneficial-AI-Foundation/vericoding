// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, c: int, prices: Seq<int>) -> bool {
    n >= 2 && prices.len() == n && c >= 0 &&
    (forall|i: int| 0 <= i < prices.len() ==> prices[i] >= 0)
}

spec fn profit_for_day(prices: Seq<int>, day: int, c: int) -> int {
    if 0 <= day < prices.len() - 1 {
        prices[day] - prices[day + 1] - c
    } else {
        0
    }
}

spec fn max_possible_profit(prices: Seq<int>, c: int) -> int {
    if prices.len() >= 2 {
        let profits = Seq::new((prices.len() - 1) as nat, |i: int| profit_for_day(prices, i, c));
        if profits.len() == 0 { 
            0 
        } else {
            let max_profit = profits[0];
            if profits.len() == 1 { 
                max_profit 
            } else { 
                seq_max(profits) 
            }
        }
    } else {
        0
    }
}

spec fn seq_max(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() > 0 {
        if s.len() == 1 { 
            s[0] 
        } else if s[0] >= seq_max(s.subrange(1, s.len() as int)) { 
            s[0] 
        } else { 
            seq_max(s.subrange(1, s.len() as int)) 
        }
    } else {
        0
    }
}

spec fn correct_result(n: int, c: int, prices: Seq<int>, result: int) -> bool {
    valid_input(n, c, prices) ==>
    (result >= 0 &&
     (result == 0 <==> (forall|i: int| 0 <= i < n - 1 ==> profit_for_day(prices, i, c) <= 0)) &&
     (result > 0 ==> (exists|i: int| 0 <= i < n - 1 && profit_for_day(prices, i, c) == result)) &&
     (forall|i: int| 0 <= i < n - 1 ==> profit_for_day(prices, i, c) <= result))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, c: i8, prices: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, c as int, prices@.map(|v| v as int))
    ensures correct_result(n as int, c as int, prices@.map(|v| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}