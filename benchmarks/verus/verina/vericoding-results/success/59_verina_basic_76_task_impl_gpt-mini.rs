// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_spec(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    let result = if x <= y { x } else { y };
    result
}
// </vc-code>

}
fn main() {}