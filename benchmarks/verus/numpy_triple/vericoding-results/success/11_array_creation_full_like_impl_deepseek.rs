// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_fill_result_property(a: Vec<f32>, fill_value: f32, result: Vec<f32>, i: int)
    requires
        0 <= i < a.len(),
        result.len() == a.len(),
        forall|j: int| 0 <= j < result.len() ==> result@[j] == fill_value,
    ensures
        result@[i] == fill_value,
{
}

proof fn lemma_fill_result_len(a: Vec<f32>, fill_value: f32, result: Vec<f32>)
    requires
        result.len() == a.len(),
        forall|j: int| 0 <= j < result.len() ==> result@[j] == fill_value,
    ensures
        result.len() == a.len(),
{
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
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> result@[j] == fill_value,
        decreases a.len() - idx,
    {
        result.push(fill_value);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}