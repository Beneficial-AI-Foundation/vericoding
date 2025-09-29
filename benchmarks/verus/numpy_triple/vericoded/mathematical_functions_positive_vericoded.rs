// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec_f32(v: Vec<f32>) -> (res: Vec<f32>)
    ensures
        res.len() == v.len(),
        forall|i: int| 0 <= i < res.len() ==> res[i] == v[i],
{
    v
}
// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
{
    let r = id_vec_f32(x);
    r
}
// </vc-code>

}
fn main() {}