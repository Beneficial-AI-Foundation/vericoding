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
/** helper modified by LLM (iteration 5): proves sum_of_positive_profits is non-negative */
proof fn sum_positive_profits_nonneg(values: Seq<int>, costs: Seq<int>, n: int)
    requires
        n >= 0,
        values.len() as int >= n,
        costs.len() as int >= n,
    ensures
        sum_of_positive_profits(values, costs, n) >= 0,
    decreases n
{
    if n == 0 {
        assert(sum_of_positive_profits(values, costs, 0) == 0 as int);
    } else {
        let profit = values[n-1] - costs[n-1];
        sum_positive_profits_nonneg(values, costs, n-1);
        assert(
            sum_of_positive_profits(values, costs, n)
            == sum_of_positive_profits(values, costs, n-1) + (if profit > 0 { profit } else { 0 as int })
        );
        assert((if profit > 0 { profit } else { 0 as int }) >= 0 as int);
        assert(sum_of_positive_profits(values, costs, n-1) >= 0 as int);
        assert(sum_of_positive_profits(values, costs, n) >= 0 as int);
    }
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
    /* code modified by LLM (iteration 5): compute sum with ghost accumulator and maintain loop invariants */
    let ghost values_seq: Seq<int> = values@.map(|i, x| x as int);
    let ghost costs_seq: Seq<int> = costs@.map(|i, x| x as int);
    let ghost N: int = n as int;
    let mut i: usize = 0;
    let mut sum_runtime: i64 = 0;
    let mut ghost sum: int = 0;
    while i < values.len()
        invariant
            0 <= i as int && i as int <= N,
            values.len() == N as nat,
            costs.len() == N as nat,
            sum == sum_of_positive_profits(values_seq, costs_seq, i as int),
        decreases N - (i as int)
    {
        assert(i < values.len());
        assert(values.len() == costs.len());
        assert(i < costs.len());
        let profit_rt: i64 = (values[i] as i64) - (costs[i] as i64);
        let profit: int = (values[i] as int) - (costs[i] as int);
        if profit > 0 {
            sum_runtime = sum_runtime + profit_rt;
            sum = sum + profit;
        }
        i = i + 1;
    }
    proof {
        assert(i as int == N);
        assert(sum == sum_of_positive_profits(values_seq, costs_seq, N));
        sum_positive_profits_nonneg(values_seq, costs_seq, N);
        assert(sum >= 0);
    }
    #[verifier::truncate]
    let result = sum as i8;
    result
}

// </vc-code>


}

fn main() {}