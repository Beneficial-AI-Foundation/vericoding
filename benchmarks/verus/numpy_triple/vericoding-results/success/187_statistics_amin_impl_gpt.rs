// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
        assert(0 <= 0);
        assert(0 < a.len());
        assert(r == a@[0]);
        assert(exists|i:int| 0 <= i && i < a.len() && r == a@[i]) by {
            assert(0 <= 0);
            assert(0 < a.len());
            assert(r == a@[0]);
        }
    }
    r
}
// </vc-code>

}
fn main() {}