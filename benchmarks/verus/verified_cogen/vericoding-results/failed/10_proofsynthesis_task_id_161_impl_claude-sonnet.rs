// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper function as it's causing verification issues */
// </vc-helpers>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): direct implementation without helper function */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(result[j]) && !arr2@.contains(result[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(arr1[j]) || result@.contains(arr1[j]))
        decreases arr1.len() - i
    {
        let element = arr1[i];
        
        if !arr2@.contains(element) {
            result.push(element);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}