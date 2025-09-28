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
/* code modified by LLM (iteration 5): use integer arithmetic to avoid overflow and fix indexing */
{
    let mut total_int: int = 0;
    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i <= n as int,
            total_int == sum_of_positive_profits(values@.map(|j,x|x as int), costs@.map(|j,x|x as int), i)
        decreases (n as int - i) as nat
    {
        proof {
            assert(values@.len() == n as int);
            assert(i < n as int);
            assert(i < values@.len());
        }
        let value_int: int = values[i as usize] as int;
        let cost_int: int = costs[i as usize] as int;
        let profit_int: int = value_int - cost_int;
        if profit_int > 0 {
            total_int = total_int + profit_int;
        }
        i = i + 1;
    }
    assert(total_int >= 0 && total_int <= 127);
    total_int as i8
}
// </vc-code>


}

fn main() {}