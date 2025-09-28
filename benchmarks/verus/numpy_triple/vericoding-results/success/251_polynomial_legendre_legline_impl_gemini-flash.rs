// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add spec block to helper function */
fn legline_helper(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == off,
        result@[1] == scl
{
    let mut v = Vec::new();
    v.push(off);
    v.push(scl);
    v
}
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == off,
        result@[1] == scl
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): call helper function */
{
    let result = legline_helper(off, scl);
    result
}
// </vc-code>

}
fn main() {}