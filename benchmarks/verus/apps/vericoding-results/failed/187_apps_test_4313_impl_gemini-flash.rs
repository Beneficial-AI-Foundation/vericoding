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
/* helper modified by LLM (iteration 5): Added a lemma for non-negativity of sum of profits. */
#[lemma]
fn lemma_sum_of_positive_profits_non_negative(
    values: Seq<int>,
    costs: Seq<int>,
    n: int,
)
    requires
        n >= 0, values.len() >= n, costs.len() >= n
    ensures
        sum_of_positive_profits(values, costs, n) >= 0
    decreases n
{
    if n > 0 {
        let profit = values[n - 1] - costs[n - 1];
        lemma_sum_of_positive_profits_non_negative(values, costs, n - 1);
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
/* code modified by LLM (iteration 5): Add proof block for total_profit non-negativity. */
{
    let mut total_profit: i16 = 0;
    let mut i: i8 = 0;

    while i < n
        invariant
            0 <= i,
            i <= n,
            total_profit as int == sum_of_positive_profits(values@.map(|k, x| x as int), costs@.map(|k, x| x as int), i as int),
            valid_input(n as int, values@.map(|k, x| x as int), costs@.map(|k, x| x as int)),
            total_profit >= 0,
        decreases n - i
    {
        let value = values[i as usize];
        let cost = costs[i as usize];
        let profit = (value as i16) - (cost as i16);

        if profit > 0 {
            total_profit = total_profit + profit;
        }

        proof {
            lemma_sum_of_positive_profits_non_negative(values@.map(|k, x| x as int), costs@.map(|k, x| x as int), (i + 1) as int);
            if profit > 0 {
                assert(total_profit >= 0);
            }
        }

        i = i + 1;
    }
    total_profit as i8
}
// </vc-code>


}

fn main() {}