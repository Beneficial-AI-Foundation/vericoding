// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): checks vector entries are non-zero */
spec fn all_nonzero(v: Vec<f32>) -> bool { forall|i: int| 0 <= i < v.len() ==> v@[i] != 0.0f32 }
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative element-wise division with corrected while invariants */
    let mut result: Vec<f32> = Vec::new();
    let len = x1.len();
    let mut i: int = 0;
    while i < len invariant 0 <= i && i <= len && result.len() == i; decreases len - i {
        let a: f32 = x1[i];
        let b: f32 = x2[i];
        let r: f32 = a / b;
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}