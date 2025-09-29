// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_total_order_i32(x: i32, y: i32)
    ensures
        x <= y || x > y
{
}

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