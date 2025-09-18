// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_pair_vec_f32(a: f32, b: f32) -> (v: Vec<f32>)
    ensures
        v.len() == 2,
        v[0] == a,
        v[1] == b
{
    let mut v = Vec::new();
    v.push(a);
    v.push(b);
    assert(v.len() == 2);
    assert(v[0] == a);
    assert(v[1] == b);
    v
}
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    let v = make_pair_vec_f32(off, scl);
    v
}
// </vc-code>

}
fn main() {}