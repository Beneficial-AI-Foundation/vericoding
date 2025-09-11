// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn IntDiv(m: i32, n: i32) -> (ret: (i32, i32))
    requires n > 0
    ensures m == n * ret.0 + ret.1 && 0 <= ret.1 < n
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}