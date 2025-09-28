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
proof fn lemma_sum_squares_minimum(a: Seq<int>, p: int)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= -100 && #[trigger] a[i] <= 100,
        -100 <= p <= 100
    ensures
        sum_squares(p, a) >= 0
    decreases a.len()
{
    if a.len() == 0 {
        assert(sum_squares(p, a) == 0);
    } else {
        let diff = p - a[0];
        assert(diff * diff >= 0);
        lemma_sum_squares_minimum(a.subrange(1, a.len() as int), p);
        assert(sum_squares(p, a.subrange(1, a.len() as int)) >= 0);
        assert(sum_squares(p, a) == diff * diff + sum_squares(p, a.subrange(1, a.len() as int)));
    }
}

/* helper modified by LLM (iteration 5): Simplified trigger in compute_sum_squares */
fn compute_sum_squares(p: i8, a: &Vec<i8>) -> (result: i8)
    requires
        a@.len() <= 100,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= -100 && a@[i] <= 100
    ensures
        result as int == sum_squares(p as int, a@.map(|_i: int, x: i8| x as int))
{
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == sum_squares(p as int, a@.map(|_j: int, x: i8| x as int).subrange(0, i as int))
        decreases a.len() - i
    {
        let diff = p - a[i];
        sum = sum + diff * diff;
        i = i + 1;
    }
    
    assert(a@.map(|_j: int, x: i8| x as int).subrange(0, a@.len() as int) =~= a@.map(|_j: int, x: i8| x as int));
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger issue by using simpler expressions */
    let mut min_cost: i8 = compute_sum_squares(-100, &a);
    let mut best_p: i8 = -100;
    let mut p: i8 = -99;
    
    proof {
        lemma_sum_squares_minimum(a@.map(|_i: int, x: i8| x as int), -100);
    }
    
    while p <= 100
        invariant
            -99 <= p <= 101,
            -100 <= best_p <= 100,
            min_cost >= 0,
            min_cost as int == sum_squares(best_p as int, a@.map(|_i: int, x: i8| x as int)),
            forall|q: int| -100 <= q < p as int ==> sum_squares(best_p as int, a@.map(|_i: int, x: i8| x as int)) <= sum_squares(q, a@.map(|_i: int, x: i8| x as int))
        decreases 101 - p
    {
        let cost = compute_sum_squares(p, &a);
        
        proof {
            lemma_sum_squares_minimum(a@.map(|_i: int, x: i8| x as int), p as int);
        }
        
        if cost < min_cost {
            min_cost = cost;
            best_p = p;
        }
        
        p = p + 1;
    }
    
    assert(forall|q: int| -100 <= q <= 100 ==> sum_squares(best_p as int, a@.map(|_i: int, x: i8| x as int)) <= sum_squares(q, a@.map(|_i: int, x: i8| x as int)));
    assert(min_cost as int == sum_squares(best_p as int, a@.map(|_i: int, x: i8| x as int)));
    
    min_cost
}
// </vc-code>


}

fn main() {}