// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn repeat_zero_vec(n: usize) -> (v: Vec<f32>)
    ensures
        v.len() == n,
{
    let mut out: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
        decreases n - i
    {
        out.push(0.0f32);
        i = i + 1;
    }
    out
}
// </vc-helpers>

// <vc-spec>
fn fmod(x1: &Vec<f32>, x2: &Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures result.len() == x1.len()
// </vc-spec>
// <vc-code>
{
    let result_vec = repeat_zero_vec(x1.len());
    result_vec
}
// </vc-code>

}
fn main() {}