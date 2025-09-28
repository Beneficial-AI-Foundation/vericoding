// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_squares(p: int, a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        (p - a[0]) * (p - a[0]) + sum_squares(p, a.subrange(1, a.len() as int))
    }
}

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && n <= 100 && a.len() == n && 
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= -100 && #[trigger] a[i] <= 100
}

spec fn is_optimal_cost(result: int, a: Seq<int>) -> bool {
    result >= 0 &&
    exists|p: int| -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall|p: int| -100 <= p <= 100 ==> result <= sum_squares(p, a)
}
// </vc-preamble>

// <vc-helpers>
lemma fn sum_squares_is_nonnegative(p: int, a: Seq<int>)
    ensures sum_squares(p, a) >= 0
    decreases a.len()
{
    if a.len() > 0 {
        sum_squares_is_nonnegative(p, a.subrange(1, a.len() as int));
    }
}

fn compute_sum_squares(p: i32, n: i8, a: &Vec<i8>) -> (result: i32)
    requires
        valid_input(n as int, a@.map(|_i, x| x as int)),
    ensures
        result as int == sum_squares(p as int, a@.map(|_i, x| x as int)),
{
    let mut total: i32 = 0;
    let mut i = (n - 1) as i32;
    let seq_a = a@.map(|_i: int, x: i8| x as int);
    while i >= 0
        invariant
            valid_input(n as int, seq_a),
            -1 <= i < n as int,
            total as int == sum_squares(p as int, seq_a.subrange(i + 1, n as int)),
        decreases i
    {
        let val = a[i as usize] as i32;
        let diff = p - val;
        total = total + diff * diff;
        i = i - 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let seq_a = a@.map(|_i: int, x: i8| x as int);

    proof { sum_squares_is_nonnegative(-100, seq_a); }
    let mut min_cost = compute_sum_squares(-100, n, &a);
    let mut p_opt = -100;

    let mut p = -99;
    while p <= 100
        invariant
            -99 <= p <= 101,
            -100 <= p_opt < p,
            min_cost as int == sum_squares(p_opt as int, seq_a),
            forall|i: int| -100 <= i < p ==> min_cost as int <= sum_squares(i, seq_a),
    {
        proof { sum_squares_is_nonnegative(p, seq_a); }
        let current_cost = compute_sum_squares(p, n, &a);
        if current_cost < min_cost {
            min_cost = current_cost;
            p_opt = p;
        }
        p = p + 1;
    }

    proof {
        assert(is_optimal_cost(min_cost as int, seq_a)) by {
            sum_squares_is_nonnegative(p_opt, seq_a);
        }
    }

    min_cost as i8
}
// </vc-code>


}

fn main() {}