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
/* helper modified by LLM (iteration 2): prove square non-negativity and strengthen sum_squares proof */
proof fn lemma_sq_nonneg(x: int)
    ensures
        x * x >= 0,
{
    assert(x * x >= 0);
}

/* helper modified by LLM (iteration 2): use recursion and unfolding to show non-negativity of sum_squares */
proof fn lemma_sum_squares_nonneg(p: int, a: Seq<int>)
    ensures
        sum_squares(p, a) >= 0,
    decreases a.len()
{
    if a.len() == 0 {
        assert(sum_squares(p, a) == 0);
    } else {
        lemma_sq_nonneg(p - a[0]);
        lemma_sum_squares_nonneg(p, a.subrange(1, a.len() as int));
        assert(sum_squares(p, a) == (p - a[0]) * (p - a[0]) + sum_squares(p, a.subrange(1, a.len() as int)));
        assert(sum_squares(p, a) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): brute-force minimal cost with safe arithmetic and loop invariants */
    let len: usize = a.len();

    // Establish len <= 100 from the precondition
    proof {
        // map preserves length
        assert(a@.map(|_i: int, x: i8| x as int).len() == a@.len());
        assert(a@.len() == len as int);
        assert(valid_input(n as int, a@.map(|_i: int, x: i8| x as int)));
        assert(a@.map(|_i: int, x: i8| x as int).len() == n as int);
        assert(len as int == n as int);
        assert(n as int <= 100);
    }

    let b: i32 = 229; // safe bound for |p - ai|
    let b2: i32 = b * b; // 52441

    let mut best_cost: i32 = 2147483647;
    let mut p: i32 = -100;
    while p <= 100
        invariant
            -100 <= p <= 101,
            best_cost >= 0,
            len == a.len(),
        decreases 101 - p as int
    {
        let mut s: i32 = 0;
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                s >= 0,
                s <= (i as i32) * b2,
                len == a.len(),
            decreases len as int - i as int
        {
            let ai: i32 = a[i] as i32;
            let d: i32 = p - ai;
            proof {
                // From types: a[i] is i8, so -128 <= a[i] <= 127
                assert(-128 <= ai && ai <= 127);
                assert(-100 <= p && p <= 101);
                // Bound d = p - ai
                assert(d <= 101 - (-128));
                assert(d >= -100 - 127);
                assert(-229 <= d && d <= 229);
                // Bound the square
                assert(0 <= d * d);
                assert(d * d <= b2);
            }
            s = s + d * d;
            i = i + 1;
        }
        if s < best_cost {
            best_cost = s;
        }
        p = p + 1;
    }
    let r: i8 = if best_cost > 127 { 127i8 } else { best_cost as i8 };
    r
}
// </vc-code>


}

fn main() {}