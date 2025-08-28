use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn valid_index(i: int, len: int) -> bool {
    0 <= i < len
}
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 0 <= j < result@.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == arr1@[j] / arr2@[j],
        decreases arr1.len() - i
    {
        assert(i < arr1.len());
        assert(i < arr2.len());
        assert(arr2[i] != 0);
        let quotient = arr1[i] / arr2[i];
        result.push(quotient);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}