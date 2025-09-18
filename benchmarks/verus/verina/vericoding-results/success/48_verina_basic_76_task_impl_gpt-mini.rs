// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns the minimum of two integers */
fn min_helper(a: i32, b: i32) -> (result: i32)
    ensures
        (a <= b ==> result == a) && (a > b ==> result == b),
{
    if a <= b {
        a
    } else {
        b
    }
}

// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call helper to compute min */
    let result: i32 = min_helper(x, y);
    result
}
// </vc-code>

}
fn main() {}