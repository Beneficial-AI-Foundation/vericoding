// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn make_vec(a: f32, b: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == a,
        result@[1] == b
{
    let mut v: Vec<f32> = Vec::new();
    v.push(a);
    v.push(b);
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
{
    /* code modified by LLM (iteration 2): Fixed compilation error by using direct vector operations */
    let mut result = Vec::new();
    result.push(off);
    result.push(scl);
    assert(result@.len() == 2);
    assert(result@[0] == off);
    assert(result@[1] == scl);
    result
}
// </vc-code>

}
fn main() {}