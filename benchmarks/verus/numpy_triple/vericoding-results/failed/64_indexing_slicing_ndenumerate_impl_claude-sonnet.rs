// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to assist with postcondition proof */
fn ndenumerate_property(arr: Vec<f32>, result: Vec<(usize, f32)>, i: usize)
    requires
        i <= arr.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> result[j].0 == j && result[j].1 == arr[j],
    ensures
        forall|j: int| 0 <= j <= i ==> j < result.len() + 1,
{}
// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed indexing consistency and proof structure */
    let mut result: Vec<(usize, f32)> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].0 == j as usize && result[j].1 == arr[j],
        decreases arr.len() - i
    {
        result.push((i, arr[i]));
        i = i + 1;
        
        proof {
            assert(result.len() == i);
            let last_idx = (i - 1) as int;
            assert(result[last_idx].0 == (i - 1));
            assert(result[last_idx].1 == arr[last_idx]);
        }
    }
    
    proof {
        assert(i == arr.len());
        assert(result.len() == arr.len());
        assert(forall|j: int| 0 <= j < result.len() ==> result[j].0 == j as usize && result[j].1 == arr[j]);
    }
    
    result
}
// </vc-code>

}
fn main() {}