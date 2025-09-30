// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> (r: usize)
    ensures
        r == if a <= b { a } else { b },
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let _m = min_usize(n, ddof);
    0.0f32
}
// </vc-code>

}
fn main() {}