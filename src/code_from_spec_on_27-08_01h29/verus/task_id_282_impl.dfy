use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            result.len() == i,
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == #[trigger] (arr1@[j] - arr2@[j]),
        decreases arr1.len() - i
    {
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}