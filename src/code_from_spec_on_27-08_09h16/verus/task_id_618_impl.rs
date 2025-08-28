use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for bounds checking
proof fn lemma_index_bounds(arr1: &Vec<u32>, arr2: &Vec<u32>, i: usize)
    requires
        arr1.len() == arr2.len(),
        i < arr1.len(),
    ensures
        i < arr2.len(),
{
}
// </vc-helpers>

// <vc-spec>
fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == arr1@[j] / arr2@[j],
            forall|j: int| 0 <= j < arr2.len() ==> arr2@[j] != 0,
        decreases arr1.len() - i
    {
        proof {
            lemma_index_bounds(arr1, arr2, i);
        }
        let div_result = arr1[i] / arr2[i];
        result.push(div_result);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}