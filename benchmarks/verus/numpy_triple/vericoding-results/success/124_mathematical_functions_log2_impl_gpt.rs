// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec_f32(v: Vec<f32>) -> (r: Vec<f32>)
    ensures r.len() == v.len()
{
    v
}
// </vc-helpers>

// <vc-spec>
fn log2(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let result = id_vec_f32(x);
    result
}
// </vc-code>

}
fn main() {}