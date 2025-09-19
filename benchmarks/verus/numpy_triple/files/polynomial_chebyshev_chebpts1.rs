// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn chebyshev_point_value(k: int, n: int) -> int { arbitrary() }

fn chebpts1(n: usize) -> (result: Vec<i8>)
    requires n > 0,
    ensures 
        result.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] result[k as int] as int == chebyshev_point_value(k, n as int),
        forall|k: int| 0 <= k < n ==> -100 <= #[trigger] result[k as int] as int <= 100,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}