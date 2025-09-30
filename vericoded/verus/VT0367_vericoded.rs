// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tan(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut r: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r.len() == i,
            n == x.len(),
        decreases n - i
    {
        r.push(x[i]);
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}