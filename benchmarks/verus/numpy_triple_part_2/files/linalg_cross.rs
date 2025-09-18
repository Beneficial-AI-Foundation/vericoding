// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_linalg_cross(x1: [i32; 3], x2: [i32; 3]) -> (result: [i32; 3])
    ensures
        result[0] == x1[1] * x2[2] - x1[2] * x2[1],
        result[1] == x1[2] * x2[0] - x1[0] * x2[2],
        result[2] == x1[0] * x2[1] - x1[1] * x2[0]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}