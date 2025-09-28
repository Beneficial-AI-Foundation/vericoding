// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn enumerate_element_proof(arr: Seq<f32>, i: nat)
    requires
        i < arr.len(),
    ensures arr[i] == arr[i as int],
{
}

proof fn nat_eq_int_lemma(n: nat)
    ensures n as int == n,
{
}
// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed array indexing with proper type conversion */
    let mut result: Vec<(usize, f32)> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < arr.len()
        invariant
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> result[j].0 == j as usize && result[j].1 == arr[j as usize],
        decreases arr.len() - idx,
    {
        proof { 
            nat_eq_int_lemma(idx as nat);
            enumerate_element_proof(arr@, idx as nat);
        }
        result.push((idx, arr[idx as usize]));
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}