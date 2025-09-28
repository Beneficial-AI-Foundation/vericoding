// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added return variable to ensures clause */
fn sort_third_helper(a: &Vec<i8>, indices: Vec<usize>) -> (result: Vec<i8>)
    requires
        a@.len() > 0,
        indices@.len() == (a@.len() + 2) / 3,
        forall|i: int| 0 <= i < indices@.len() ==> indices@[i] < a@.len() as nat && indices@[i] % 3 == 0,
        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> indices@[i] < indices@[j]
    ensures
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() && i % 3 != 0 ==> result@[i] == a@[i],
        forall|i: int, j: int| 0 <= i < j < result@.len() && i % 3 == 0 && j % 3 == 0 ==> result@[i] <= result@[j],
        a@.to_multiset() == result@.to_multiset()
{
    let mut res = a.clone();
    let mut values = Vec::new();
    
    // Extract values at indices divisible by 3
    for i in 0..indices.len()
    {
        values.push(a[indices[i]]);
    }
    
    // Sort the extracted values
    values.sort();
    
    // Place sorted values back at indices divisible by 3
    for i in 0..indices.len()
    {
        res[indices[i]] = values[i];
    }
    
    res
}
// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed */
{
    let mut indices = Vec::new();
    
    // Collect indices divisible by 3
    for i in 0..a.len()
    {
        if i % 3 == 0 {
            indices.push(i);
        }
    }
    
    sort_third_helper(a, indices)
}
// </vc-code>


}

fn main() {}