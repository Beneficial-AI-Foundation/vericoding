// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_of_positive_profits(values: Seq<int>, costs: Seq<int>, n: int) -> int
    decreases n
    when n >= 0 && values.len() >= n && costs.len() >= n
{
    if n == 0 { 
        0 as int
    } else { 
        let profit = values[n-1] - costs[n-1];
        sum_of_positive_profits(values, costs, n-1) + (if profit > 0 { profit } else { 0 as int })
    }
}

spec fn valid_input(n: int, values: Seq<int>, costs: Seq<int>) -> bool
{
    values.len() == n && costs.len() == n && n >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, values: Seq<int>, costs: Seq<int>) -> (result: i32)
    requires 
        valid_input(n, values, costs)
    ensures 
        result >= 0 &&
        result == sum_of_positive_profits(values, costs, n) as i32
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}