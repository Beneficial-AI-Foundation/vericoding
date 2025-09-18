// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
spec fn is_nonneg(x: int) -> bool { x >= 0 }
// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
{
    if x >= 0 {
        x
    } else {
        0 - x
    }
}
// </vc-code>

}
fn main() {}