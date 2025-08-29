use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn element_at_bounds<T>(v: &Vec<T>, i: usize) 
    requires i < v.len()
    ensures 0 <= i < v@.len()
{
}

proof fn precondition_holds_at_index(arr1: &Vec<u32>, arr2: &Vec<u32>, i: usize)
    requires 
        i < arr1.len(),
        arr1.len() == arr2.len(),
        forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
    ensures arr2@[i as int] != 0
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): added precondition proof for non-zero element */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (arr1@[j] % arr2@[j]),
        decreases arr1.len() - i,
    {
        proof { 
            element_at_bounds(arr2, i);
            precondition_holds_at_index(arr1, arr2, i);
        }
        let mod_result = arr1[i] % arr2[i];
        result.push(mod_result);
        i += 1;
    }
    
    result
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}