use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<u32> = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
            forall|m: int| 0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m] <= u32::MAX),
            forall|k: int| 0 <= k < i ==> #[trigger] result[k] == #[trigger] (arr1[k] / arr2[k]),
        decreases arr1.len() - i,
    {
        let div_result = arr1[i] / arr2[i];
        result.push(div_result);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}