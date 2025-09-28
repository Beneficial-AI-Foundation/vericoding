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
/* helper modified by LLM (iteration 2): define positive part and unfolding/nonnegativity lemmas for reasoning */
spec fn pos_part(x: int) -> int { if x > 0 { x } else { 0 } }

/* helper modified by LLM (iteration 2): lemma unfolding the recursive definition */
proof fn lemma_sum_of_positive_profits_unfold(values: Seq<int>, costs: Seq<int>, n: int)
    requires
        n >= 0,
        values.len() >= n,
        costs.len() >= n,
    ensures
        if n == 0 {
            sum_of_positive_profits(values, costs, n) == 0
        } else {
            let profit = values[n - 1] - costs[n - 1];
            sum_of_positive_profits(values, costs, n) == sum_of_positive_profits(values, costs, n - 1) + pos_part(profit)
        },
{
    if n == 0 {
        assert(sum_of_positive_profits(values, costs, n) == 0);
    } else {
        let profit = values[n - 1] - costs[n - 1];
        assert(pos_part(profit) == (if profit > 0 { profit } else { 0 }));
        assert(sum_of_positive_profits(values, costs, n)
            == sum_of_positive_profits(values, costs, n - 1)
             + (if profit > 0 { profit } else { 0 }));
        assert(sum_of_positive_profits(values, costs, n)
            == sum_of_positive_profits(values, costs, n - 1) + pos_part(profit));
    }
}

/* helper modified by LLM (iteration 2): lemma showing pos_part is nonnegative */
proof fn lemma_pos_part_nonneg(x: int)
    ensures
        pos_part(x) >= 0,
{
    if x > 0 {
        assert(pos_part(x) == x);
        assert(pos_part(x) >= 0);
    } else {
        assert(pos_part(x) == 0);
        assert(pos_part(x) >= 0);
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
    /* code modified by LLM (iteration 2): compute using machine integers only; move 'int' reasoning into proof blocks */
    let nn: usize = values.len();

    // Establish both vectors have the same length
    proof {
        assert(values@.len() == n as int);
        assert(costs@.len() == n as int);
        assert(values@.len() == costs@.len());
        assert(values@.len() == values.len() as int);
        assert(costs@.len() == costs.len() as int);
        assert(values.len() as int == costs.len() as int);
        assert(values.len() == costs.len());
    }

    let mut i: usize = 0;
    let mut acc_i32: i32 = 0;

    while i < nn
        invariant
            i <= nn,
            nn == values.len(),
            nn == costs.len(),
            acc_i32 as int == sum_of_positive_profits(values@.map(|j, x| x as int), costs@.map(|j, x| x as int), i as int),
            acc_i32 >= 0,
        decreases nn - i
    {
        let v_i: i8 = values[i];
        let c_i: i8 = costs[i];
        let diff_i32: i32 = (v_i as i32) - (c_i as i32);
        let add_i32: i32 = if diff_i32 > 0 { diff_i32 } else { 0 };

        proof {
            let diff_int: int = (v_i as int) - (c_i as int);
            lemma_pos_part_nonneg(diff_int);
            if diff_int > 0 {
                assert(add_i32 as int == diff_int);
            } else {
                assert(add_i32 == 0);
                assert(add_i32 as int == 0);
            }
            lemma_sum_of_positive_profits_unfold(
                values@.map(|j, x| x as int),
                costs@.map(|j, x| x as int),
                (i as int) + 1,
            );
        }

        acc_i32 = acc_i32 + add_i32;
        i = i + 1;
    }

    let result_i8: i8 = acc_i32 as i8;
    result_i8
}
// </vc-code>


}

fn main() {}