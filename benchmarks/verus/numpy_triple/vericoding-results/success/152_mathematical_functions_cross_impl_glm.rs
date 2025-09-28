// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): use wrapping arithmetic to prevent overflow */
    let c0 = a[1].wrapping_mul(b[2]).wrapping_sub(a[2].wrapping_mul(b[1]));
    let c1 = a[2].wrapping_mul(b[0]).wrapping_sub(a[0].wrapping_mul(b[2]));
    let c2 = a[0].wrapping_mul(b[1]).wrapping_sub(a[1].wrapping_mul(b[0]));
    vec![c0, c1, c2]
}
// </vc-code>

}
fn main() {}