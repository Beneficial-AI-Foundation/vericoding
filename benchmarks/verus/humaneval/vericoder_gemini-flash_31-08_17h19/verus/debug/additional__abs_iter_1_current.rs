use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs(x: i32) -> (result: i32)
    // pre-conditions-start
    requires
        x != i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result >= 0,
        result == x || result == -x,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    if x >= 0 {
        x
    } else {
        // Since x != i32::MIN, -x is guaranteed to not overflow.
        // i32::MIN is the only value for which -x would overflow.
        -x
    }
    // impl-end
}
// </vc-code>

fn main() {}
}