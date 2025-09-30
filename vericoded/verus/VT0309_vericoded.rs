// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn exp2(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut out: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            out.len() == i,
        decreases x.len() as int - i as int
    {
        out.push(x[i]);
        i += 1;
    }
    out
}
// </vc-code>


}
fn main() {}