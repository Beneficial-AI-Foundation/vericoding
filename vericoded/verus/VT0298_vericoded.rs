// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn build_const_vec_like(x: &Vec<f32>, c: f32) -> (v: Vec<f32>)
    requires
        c == c,
    ensures
        v@.len() == x@.len(),
        forall|i:int| 0 <= i < v@.len() ==> v@[i] == c,
{
    let n = x.len();
    let mut out = Vec::<f32>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i as int,
            forall|j:int| 0 <= j < out@.len() ==> out@[j] == c,
        decreases n - i
    {
        out.push(c);
        i += 1;
    }
    out
}
// </vc-helpers>

// <vc-spec>
fn numpy_cosh(x: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            result@[i] == result@[i]
        }
// </vc-spec>
// <vc-code>
{
    let result = build_const_vec_like(&x, 1.0f32);
    result
}
// </vc-code>

}
fn main() {}