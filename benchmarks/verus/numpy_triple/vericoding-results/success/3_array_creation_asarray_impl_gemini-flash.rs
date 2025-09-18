// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn asarray(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed missing decreases clause in loop */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == a[j]
        decreases a.len() - i
    {
        result_vec.push(a[i as usize]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}