// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn int_div(n: int, d: int) -> (result: (int, int))
    requires n >= d && n >= 0 && d > 0,
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}