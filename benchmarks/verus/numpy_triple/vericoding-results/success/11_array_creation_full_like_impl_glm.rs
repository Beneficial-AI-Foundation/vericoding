// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added i <= len to loop invariant to prove postcondition */
fn create_filled_vector(len: usize, fill_value: f32) -> (result: Vec<f32>)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
{
    if len == 0 {
        Vec::new()
    } else {
        let mut result = Vec::with_capacity(len);
        let mut i = 0;
        while i < len
            invariant
                i <= len,
                result.len() == i,
                forall|j: int| 0 <= j < result.len() ==> result[j] == fill_value,
            decreases len - i,
        {
            result.push(fill_value);
            i += 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Use helper function to create filled vector */
    let len = a.len();
    create_filled_vector(len, fill_value)
}
// </vc-code>

}
fn main() {}