// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): remove redundant function signature */
// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added decreases clause for loop */
{
    let mut result_vec: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == x[j],
        decreases x.len() - i
    {
        result_vec.push(x[i]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}