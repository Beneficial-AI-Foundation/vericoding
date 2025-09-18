// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added `new` function to initialize Vec */ /* Fix: Compilation error */
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize Vec correctly and populate it */ {
    let mut result: Vec<f32> = Vec::new();
    result.push(off);
    result.push(scl);
    result
}
// </vc-code>

}
fn main() {}