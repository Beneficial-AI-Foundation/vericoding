// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mk_pair(off: f32, scl: f32) -> (v: Vec<f32>)
    ensures
        v@.len() == 2,
        v@[0] == off,
        v@[1] == scl,
{
    let mut v: Vec<f32> = Vec::new();
    v.push(off);
    v.push(scl);
    v
}
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == off,
        result@[1] == scl
// </vc-spec>
// <vc-code>
{
    let result = mk_pair(off, scl);
    result
}
// </vc-code>

}
fn main() {}