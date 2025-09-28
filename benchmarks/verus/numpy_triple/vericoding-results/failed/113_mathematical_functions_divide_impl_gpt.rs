// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn fdiv(a: f32, b: f32) -> f32 {
    a / b
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut out: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out.len() == i,
            x1.len() == n,
            x2.len() == n,
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        let c = fdiv(a, b);
        out.push(c);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}