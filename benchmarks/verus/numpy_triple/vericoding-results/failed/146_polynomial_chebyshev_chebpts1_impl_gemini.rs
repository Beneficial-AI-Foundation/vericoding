// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate spec function to fix compilation error */
fn compute_chebyshev_point(k: usize, n: usize) -> (point: i32)
    requires
        n > 0,
        k < n,
    ensures
        -1000 <= point <= 1000,
        point == chebyshev_point_value(k as int, n as int),
{
    if n == 1 {
        0i32
    } else {
        let ki = k as i64;
        let ni = n as i64;
        (1000i64 - (2000i64 * ki) / (ni - 1i64)) as i32
    }
}

// </vc-helpers>

// <vc-spec>
spec fn chebyshev_point_value(k: int, n: int) -> int { arbitrary() }

fn chebpts1(n: usize) -> (result: Vec<i32>)
    requires n > 0,
    ensures 
        result.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] result@[k] == chebyshev_point_value(k, n as int),
        forall|k: int| 0 <= k < n ==> -1000 <= #[trigger] result@[k] <= 1000,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes, loop implementation is correct */
{
    let mut result = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n
        invariant
            n > 0,
            k <= n,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] result@[i] == chebyshev_point_value(i, n as int),
            forall|i: int| 0 <= i < k ==> -1000 <= #[trigger] result@[i] <= 1000,
        decreases n - k
    {
        let val = compute_chebyshev_point(k, n);
        result.push(val);
        k = k + 1;
    }
    result
}

// </vc-code>


}
fn main() {}