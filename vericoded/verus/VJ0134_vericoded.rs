// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs(x: i32) -> (result: i32)
    requires
        x != i32::MIN,
    ensures
        result >= 0,
        result == x || result == -x,
// </vc-spec>
// <vc-code>
{
    if x >= 0 {
        x
    } else {
        assert(x != i32::MIN);
        -x
    }
}
// </vc-code>

}
fn main() {}