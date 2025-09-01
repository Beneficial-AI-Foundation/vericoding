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
    if x < 0 {
        assert(x >= i32::MIN + 1);
        assert(-x <= i32::MAX);
        -x
    } else {
        x
    }
}
// </vc-code>

fn main() {}
}