// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed spec using unsupported f32::floor to fix compilation. */
#[verifier(external_body)]
fn rint_one(f: f32) -> (res: f32)
{
    let y = f.floor();
    let r = f - y;
    if r < 0.5 {
        y
    } else if r > 0.5 {
        y + 1.0
    } else {
        if y % 2.0 == 0.0 {
            y
        } else {
            y + 1.0
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_rint(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): No change as the implementation is correct and verifies with the fixed helper function. */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        let rounded_val = rint_one(val);
        result.push(rounded_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}