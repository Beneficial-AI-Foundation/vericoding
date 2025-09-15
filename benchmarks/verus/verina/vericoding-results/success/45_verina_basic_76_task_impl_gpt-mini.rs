// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): pure spec-level min for i32 */
spec fn min_i32(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): return conditional directly to satisfy postcondition */
    if x <= y {
        x
    } else {
        y
    }
}
// </vc-code>

}
fn main() {}