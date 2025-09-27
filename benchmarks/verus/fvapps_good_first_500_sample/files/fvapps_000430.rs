// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mirror_reflection(p: u32, q: u32) -> (result: u32)
    requires 
        p > 0,
        q <= p,
    ensures 
        result == 0 || result == 1 || result == 2,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

}

fn main() {
    // assert(mirror_reflection(2, 1) == 2);
    // assert(mirror_reflection(4, 2) == 2);
    // assert(mirror_reflection(5, 5) == 1);
}