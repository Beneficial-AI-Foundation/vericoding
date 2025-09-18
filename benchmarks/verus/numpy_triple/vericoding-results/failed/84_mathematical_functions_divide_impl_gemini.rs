// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed while-loop invariant syntax, as invariants cannot be comma-separated. */
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < x1.len() as int
        decreases x1.len() as int - i
        invariant x1.len() == x2.len()
        invariant 0 <= i && i <= x1.len() as int
        invariant result.len() == i as usize
        invariant forall|j: int| 0 <= j < i ==> x2@[j] != 0.0f32
    {
        assert(x2@[i] != 0.0f32);
        let div = x1[i as usize] / x2[i as usize];
        result.push(div);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}