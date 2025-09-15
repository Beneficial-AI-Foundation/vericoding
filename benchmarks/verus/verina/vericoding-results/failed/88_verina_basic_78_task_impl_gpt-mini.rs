// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sub_add_cancel(x: i32, y: i32) ensures x - y + y == x { }
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    let r0: i32 = x + y;
    let r1: i32 = x - y;
    proof {
        assert(r1 + y == x);
    }
    (r0, r1)
}
// </vc-code>

}
fn main() {}