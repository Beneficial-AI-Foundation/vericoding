// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial proof helper */
proof fn trivial_helper() {
    assert(true);
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simple multiplication using built-in operator */
    let result: i32 = a * b;
    result
}
// </vc-code>

}
fn main() {}