// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_non_negative(x: i32) -> bool { x >= 0 }
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
    let result: i32 = if x >= 0 { x } else { -x };
    result
}
// </vc-code>

}
fn main() {}