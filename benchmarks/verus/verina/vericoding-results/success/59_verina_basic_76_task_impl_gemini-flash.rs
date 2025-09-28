// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed function to a ghost function to allow verification, and simplified the implementation */
spec fn my_min_spec(x: i32, y: i32) -> i32 {
    if x < y { x } else { y }
}
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed implementation using an if/else expression directly */
{
    let result: i32;
    if x < y {
        result = x;
    } else {
        result = y;
    }
    result
}
// </vc-code>

}
fn main() {}