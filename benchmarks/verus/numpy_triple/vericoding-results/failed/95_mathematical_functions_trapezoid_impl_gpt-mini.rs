// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): all_equal spec */
spec fn all_equal(y: Vec<i32>) -> bool { forall|i: int| 0 <= i && i < (y.len() as int) ==> y[i as usize] == y[0] }

/* helper modified by LLM (iteration 5): all_nonneg spec */
spec fn all_nonneg(y: Vec<i32>) -> bool { forall|i: int| 0 <= i && i < (y.len() as int) ==> y[i as usize] >= 0 }

/* helper modified by LLM (iteration 5): pair_prefix_sum spec */
spec fn pair_prefix_sum(y: Vec<i32>, k: int) -> i32
    requires y.len() as int >= 1, 0 <= k && k <= (y.len() as int) - 1
    decreases k
{ if k == 0 { 0 } else { pair_prefix_sum(y, k-1) + y[(k-1) as usize] + y[k as usize] } }

/* helper modified by LLM (iteration 5): proof for all equal */
proof fn pair_prefix_sum_all_equal_rec(y: Vec<i32>, k: int)
    requires y.len() as int >= 1, 0 <= k && k <= (y.len() as int) - 1, all_equal(y)
    ensures pair_prefix_sum(y, k) == 2 * k as i32 * y[0]
    decreases k
{
    if k == 0 {
    } else {
        pair_prefix_sum_all_equal_rec(y, k-1);
        assert(pair_prefix_sum(y, k) == pair_prefix_sum(y, k-1) + y[(k-1) as usize] + y[k as usize]);
        assert(pair_prefix_sum(y, k-1) == 2 * (k-1) as i32 * y[0]);
        assert(y[(k-1) as usize] == y[0]);
        assert(y[k as usize] == y[0]);
        assert(pair_prefix_sum(y, k) == 2 * (k-1) as i32 * y[0] + y[0] + y[0]);
        assert(pair_prefix_sum(y, k) == 2 * k as i32 * y[0]);
    }
}

/* helper modified by LLM (iteration 5): proof for nonneg */
proof fn pair_prefix_sum_nonneg_rec(y: Vec<i32>, k: int)
    requires y.len() as int >= 1, 0 <= k && k <= (y.len() as int) - 1, all_nonneg(y)
    ensures pair_prefix_sum(y, k) >= 0
    decreases k
{
    if k == 0 {
    } else {
        pair_prefix_sum_nonneg_rec(y, k-1);
        assert(pair_prefix_sum(y, k) == pair_prefix_sum(y, k-1) + y[(k-1) as usize] + y[k as usize]);
        assert(pair_prefix_sum(y, k-1) >= 0);
        assert(y[(k-1) as usize] >= 0);
        assert(y[k as usize] >= 0);
        assert(pair_prefix_sum(y, k) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i32>, dx: i32) -> (result: i32)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] == y[0]) ==> 
            result == dx * (y.len() - 1) as i32 * y[0],
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute pairwise sum via loop with single invariant line */
    let n: int = y.len() as int;
    let mut i: int = 0;
    let mut sum: i32 = 0;
    while i + 1 < n
        invariant 0 <= i && i <= n - 1 && sum == pair_prefix_sum(y, i);
        decreases n - 1 - i
    {
        sum = sum + y[i as usize] + y[(i + 1) as usize];
        i = i + 1;
    }
    assert(sum == pair_prefix_sum(y, n - 1));
    let result = dx * sum / 2;
    if all_equal(y) {
        proof {
            pair_prefix_sum_all_equal_rec(y, n - 1);
            assert(sum == 2 * (n - 1) as i32 * y[0]);
            assert(result == dx * (n - 1) as i32 * y[0]);
        }
    }
    if all_nonneg(y) {
        proof {
            pair_prefix_sum_nonneg_rec(y, n - 1);
            assert(sum >= 0);
            assert(result >= 0);
        }
    }
    result
}
// </vc-code>

}
fn main() {}