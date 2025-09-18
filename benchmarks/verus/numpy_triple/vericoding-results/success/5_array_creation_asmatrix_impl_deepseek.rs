// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


spec fn vector_index_equals_itself<T>(v: Vec<T>, i: int) -> bool {
    v@.index(i) == v@[i]
}

proof fn vector_reconstruction_proof(data: Vec<f32>) 
    ensures 
        forall|i: int| 0 <= i < data.len() ==> data@[i] == data@.index(i)
{
}

// </vc-helpers>

// <vc-spec>
fn asmatrix(data: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to loop */
    let mut result = Vec::new();
    proof {
        vector_reconstruction_proof(data);
    }
    let mut i = 0;
    while i < data.len()
        invariant 
            0 <= i <= data.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == data@[j]
        decreases data.len() - i
    {
        result.push(data[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}