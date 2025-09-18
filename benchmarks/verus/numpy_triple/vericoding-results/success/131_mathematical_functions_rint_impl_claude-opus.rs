// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_rint(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}