// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected the return type of `abs_i32` to `i32` for both branches to fix a compilation error. */
spec fn abs_i32(x: i32) -> i32 { if x >= 0 { x } else { -x } }
// </vc-helpers>

// <vc-spec>
fn abs_impl(x: i32) -> (result: i32)
    ensures
        (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The implementation was already correct; only the helper function needed a fix, so this code remains unchanged. */
{
    let result = abs_i32(x);
    result
}
// </vc-code>

}
fn main() {}