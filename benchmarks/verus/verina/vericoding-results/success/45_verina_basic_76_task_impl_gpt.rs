// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_i32_spec(x: i32, y: i32) -> i32 { if x <= y { x } else { y } }
proof fn lemma_min_i32_spec(x: i32, y: i32)
    ensures
        (x <= y ==> min_i32_spec(x, y) == x) &&
        (x > y ==> min_i32_spec(x, y) == y)
{ }
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
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