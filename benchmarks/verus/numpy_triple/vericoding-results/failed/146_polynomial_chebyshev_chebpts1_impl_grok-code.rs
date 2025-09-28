// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < n 
        invariant
            result.len() == k,
            0 <= k <= n,
        decreases n - k
    {
        result.push(0);
        k += 1;
    }
    result
}
// </vc-code>


}
fn main() {}