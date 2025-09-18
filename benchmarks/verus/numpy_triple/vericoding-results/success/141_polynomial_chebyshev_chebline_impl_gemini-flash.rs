// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed duplicate `chebline` function */
// </vc-helpers>

// <vc-spec>
fn chebline(off: f32, scl: f32) -> (result: [f32; 2])
    ensures 
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implement the `chebline` function logic */
{
    let result: [f32; 2] = [off, scl];
    result
}
// </vc-code>

}
fn main() {}