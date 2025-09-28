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
/* helper modified by LLM (iteration 5): Added trigger annotations to fix quantifier trigger inference */
proof fn lemma_sum_squares_monotonic(p1: int, p2: int, a: Seq<int>)
    requires
        p1 <= p2,
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= -100 && a[i] <= 100
    ensures
        sum_squares(p1, a) >= sum_squares(p2, a) ==> p1 >= (p2 + a.first()) / 2
{
}

proof fn lemma_optimal_exists(a: Seq<int>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= -100 && a[i] <= 100
    ensures
        exists|p: int| #[trigger] sum_squares(p, a) >= 0 && -100 <= p <= 100 && forall|q: int| -100 <= q <= 100 ==> #[trigger] sum_squares(p, a) <= #[trigger] sum_squares(q, a)
{
}

proof fn lemma_sum_squares_compute(p: int, a: Seq<int>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= -100 && a[i] <= 100
    ensures
        sum_squares(p, a) == (p - a[0]) * (p - a[0]) + sum_squares(p, a.subrange(1, a.len() as int))
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotation to fix quantifier trigger inference */
    let mut best_cost = i8::MAX;
    let mut p = -100i8;
    
    while p <= 100
        invariant
            -100 <= p <= 101,
            best_cost >= 0,
            forall|test_p: int| -100 <= test_p < p ==> best_cost as int <= #[trigger] sum_squares(test_p, a@.map(|_i: int, x: i8| x as int))
        decreases 100 - p
    {
        let mut cost = 0i8;
        let mut i = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                cost >= 0,
                cost as int == sum_squares(p as int, a@.map(|_i: int, x: i8| x as int).subrange(0, i as int))
            decreases n - i
        {
            let diff = p - a[i as usize];
            cost = cost + diff * diff;
            i = i + 1;
        }
        
        if cost < best_cost {
            best_cost = cost;
        }
        p = p + 1;
    }
    
    best_cost
}
// </vc-code>


}

fn main() {}