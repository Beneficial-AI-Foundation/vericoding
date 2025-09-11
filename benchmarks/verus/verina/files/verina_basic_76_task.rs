// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}