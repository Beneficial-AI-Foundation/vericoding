// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut v = Vec::new();
    v.push(off);
    v.push(scl);
    proof {
        assert(v@.len() == 2);
        assert(v@[0] == off);
        assert(v@[1] == scl);
    }
    v
}
// </vc-code>

}
fn main() {}