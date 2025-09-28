// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [Removed requires/ensures from spec function to fix compilation error.] */
spec fn cross_product_spec(a: Seq<int>, b: Seq<int>) -> Seq<int>
{
    seq![
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0]
    ]
}
// </vc-helpers>

// <vc-spec>
fn cross(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == 3,
        b.len() == 3,
    ensures 
        result.len() == 3,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [Fixed a typo in the cross product formula for the second component.] */
{
    let cx = a[1].wrapping_mul(b[2]).wrapping_sub(a[2].wrapping_mul(b[1]));
    let cy = a[2].wrapping_mul(b[0]).wrapping_sub(a[0].wrapping_mul(b[2]));
    let cz = a[0].wrapping_mul(b[1]).wrapping_sub(a[1].wrapping_mul(b[0]));
    vec![cx, cy, cz]
}
// </vc-code>

}
fn main() {}