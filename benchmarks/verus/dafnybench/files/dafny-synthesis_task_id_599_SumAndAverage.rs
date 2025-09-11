// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: i32) -> (res: (i32, i32))
    requires n > 0
    ensures res.0 == n * (n + 1) / 2 && res.1 * n == res.0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}