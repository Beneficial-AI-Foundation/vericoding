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
proof fn lemma_sum_zero(values: Seq<int>, costs: Seq<int>)
    ensures
        sum_of_positive_profits(values, costs, 0) == 0
{
    // by definition
}

proof fn lemma_sum_induct(values: Seq<int>, costs: Seq<int>, n: int)
    requires
        n > 0,
        values.len() >= n,
        costs.len() >= n
    ensures
        sum_of_positive_profits(values, costs, n) ==
            sum_of_positive_profits(values, costs, n - 1) +
            (if (values[n-1] - costs[n-1]) > 0 { values[n-1] - costs[n-1] } else { 0 })
{
    // unfolds the recursion
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
    /* code modified by LLM (iteration 5): fixed compilation error by using exec type i32 for result_int and profit */
    let ghost values_seq = values@.map(|i, x| x as int);
    let ghost costs_seq = costs@.map(|i, x| x as int);
    let mut i: usize = 0;
    let n_usize = n as usize;
    let mut result_int: i32 = 0;
    proof {
        lemma_sum_zero(values_seq, costs_seq);
        assert(result_int == sum_of_positive_profits(values_seq, costs_seq, i as int));
    }
    while i < n_usize
        invariant
            0 <= i as int <= n_usize as int,
            valid_input(n as int, values_seq, costs_seq),
            result_int as int == sum_of_positive_profits(values_seq, costs_seq, i as int),
            i <= values.len(),
            i <= costs.len(),
        decreases n_usize - i
    {
        let profit = values[i] as i32 - costs[i] as i32;
        let add_val = if profit > 0 { profit as i32 } else { 0 };
        result_int = result_int + add_val;
        proof {
            lemma_sum_induct(values_seq, costs_seq, (i + 1) as int);
            assert(add_val as int == if (values_seq[i as int] - costs_seq[i as int]) > 0 { values_seq[i as int] - costs_seq[i as int] } else { 0 });
            assert(result_int as int == sum_of_positive_profits(values_seq, costs_seq, (i + 1) as int));
        }
        i = i + 1;
    }
    result_int as i8
}
// </vc-code>


}

fn main() {}