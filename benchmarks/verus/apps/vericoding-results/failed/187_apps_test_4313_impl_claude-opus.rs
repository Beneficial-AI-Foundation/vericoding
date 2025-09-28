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
fn solve(n: i8, values: Vec<i8>, costs: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, values@.map(|i, x| x as int), costs@.map(|i, x| x as int))
    ensures 
        result >= 0 &&
        result as int == sum_of_positive_profits(values@.map(|i, x| x as int), costs@.map(|i, x| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification error */
    let mut total: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            values.len() == n as usize,
            costs.len() == n as usize,
            n >= 0,
            total >= 0,
            total as int == sum_of_positive_profits(values@.map(|j, x| x as int), costs@.map(|j, x| x as int), i as int),
        decreases n as usize - i
    {
        let profit = values[i] - costs[i];
        if profit > 0 {
            total = total + profit;
        }
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}