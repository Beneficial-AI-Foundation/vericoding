// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn in_array(result: f32, a: Seq<f32>) -> bool {
    exists|i: int| 0 <= i < a.len() && result == a[i]
}

fn amin(a: Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures in_array(result, a@),
// </vc-spec>
// <vc-code>
{
    let r = a[0];
    proof {
        assert(in_array(r, a@)) by {
            let i: int = 0;
            assert(0 <= i);
            assert(a@.len() == a.len() as int);
            assert(i < a@.len());
            assert(r == a@[i]);
        }
    }
    r
}
// </vc-code>

}
fn main() {}