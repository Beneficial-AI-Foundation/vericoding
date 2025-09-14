// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn arithmetic_weird_helper() { assert(0 < 10); }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): proper function implementation with proof */
    let x: i32 = 5;
    let y: i32 = 3;
    let z = x * y - x - y; // 5*3 - 5 - 3 = 15-5-3 = 7
    proof { assert(z < 10); }
    z
}
// </vc-code>

}
fn main() {}