// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed unused helper */
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implement the min function directly */
{
    if x <= y {
        x
    } else {
        y
    }
}
// </vc-code>

}
fn main() {}