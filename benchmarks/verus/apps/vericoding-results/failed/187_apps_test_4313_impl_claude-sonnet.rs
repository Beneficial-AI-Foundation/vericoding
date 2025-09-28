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
/* helper modified by LLM (iteration 5): fixed int literal syntax by removing suffix */
fn sum_of_positive_profits_nonnegative(values: Seq<int>, costs: Seq<int>, n: int)
    requires
        n >= 0,
        values.len() >= n,
        costs.len() >= n,
    ensures
        sum_of_positive_profits(values, costs, n) >= 0,
    decreases n
{
    if n > 0 {
        sum_of_positive_profits_nonnegative(values, costs, n-1);
    }
}

fn sum_of_positive_profits_base_case(values: Seq<int>, costs: Seq<int>)
    requires
        values.len() >= 0,
        costs.len() >= 0,
    ensures
        sum_of_positive_profits(values, costs, 0) == 0,
{
}
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
    /* code modified by LLM (iteration 5): fixed indexing to use usize instead of int */
    let mut result: i8 = 0;
    let mut i: i8 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result >= 0,
            result as int == sum_of_positive_profits(values@.map(|j, x| x as int), costs@.map(|j, x| x as int), i as int),
    {
        let profit = values[i as usize] - costs[i as usize];
        if profit > 0 {
            result = result + profit;
        }
        i = i + 1;
        
        proof {
            sum_of_positive_profits_nonnegative(values@.map(|j, x| x as int), costs@.map(|j, x| x as int), i as int);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}