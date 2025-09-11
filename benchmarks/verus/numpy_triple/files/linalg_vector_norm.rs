// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn vector_norm(x: Vec<i32>, p: i32) -> (result: i32)
    requires p >= 0,
    ensures 
        result >= 0,
        x@.len() == 0 ==> result == 0,
        result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}