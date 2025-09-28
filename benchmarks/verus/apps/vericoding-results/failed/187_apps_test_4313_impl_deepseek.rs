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

/* helper modified by LLM (iteration 5): remove assume from proof */
proof fn sum_positive_equiv()
    ensures
        forall |values: Seq<int>, costs: Seq<int>, n: int|
            n >= 0 && values.len() >= n && costs.len() >= n
            ==> sum_of_positive_profits(values, costs, n) 
                == sum_positive(values.zip_with(costs, |v, c| v - c), n, 0),
{
    assert forall |values: Seq<int>, costs: Seq<int>, n: int|
        n >= 0 && values.len() >= n && costs.len() >= n
        implies sum_of_positive_profits(values, costs, n) 
                == sum_positive(values.zip_with(costs, |v, c| v - c), n, 0) by {
        
        let merged = values.zip_with(costs, |v, c| v - c);
        if n == 0 {
            assert(sum_of_positive_profits(values, costs, 0) == 0);
            assert(sum_positive(merged, 0, 0) == 0);
        } else {
            let sub_values = values.subrange(0, n-1);
            let sub_costs = costs.subrange(0, n-1);
            let sub_merged = sub_values.zip_with(sub_costs, |v, c| v - c);
            
            assert(sub_values.len() == n-1 && sub_costs.len() == n-1);
            assert(sub_merged == merged.subrange(0, n-1));
            
            let induction_hyp = sum_of_positive_profits(sub_values, sub_costs, n-1) 
                == sum_positive(sub_merged, n-1, 0);
            
            let profit_val = values[n-1] - costs[n-1];
            let prev_sum = sum_of_positive_profits(values, costs, n-1);
            assert(prev_sum == sum_of_positive_profits(sub_values, sub_costs, n-1));
            
            assert(sum_of_positive_profits(values, costs, n) == prev_sum + (if profit_val > 0 { profit_val } else { 0 }));
            assert(merged[n-1] == profit_val);
            assert(sum_positive(merged, n, 0) == sum_positive(merged, n-1, 0) + (if profit_val > 0 { profit_val } else { 0 }));
            assert(sum_positive(merged, n-1, 0) == sum_positive(sub_merged, n-1, 0));
        }
    };
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
    /* code modified by LLM (iteration 5): fix compilation error with implies syntax */
    let mut result: i8 = 0;
    let mut idx: usize = 0;
    let values_seq = values@.map(|i, x| x as int);
    let costs_seq = costs@.map(|i, x| x as int);
    
    while idx < n as usize
        invariant
            idx <= n as usize,
            result as int == sum_of_positive_profits(values_seq, costs_seq, idx as int),
            result >= 0,
    {
        let profit: i8 = values[idx] - costs[idx];
        if profit > 0 {
            result = result + profit;
        }
        idx = idx + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}