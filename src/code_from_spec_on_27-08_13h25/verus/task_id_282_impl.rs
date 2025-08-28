use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut result: Vec<i32> = Vec::new();
    let len = arr1.len();
    let mut i: usize = 0;

    while i < len
        invariant
            len == arr1.len(),
            len == arr2.len(),
            i <= len,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k as usize] == #[trigger] (arr1[k as usize] - arr2[k as usize]),
        decreases len - i
    {
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i = i + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}