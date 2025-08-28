use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

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
    let mut result: Vec<u32> = Vec::new();
    let len = arr1.len();
    let mut i: usize = 0;

    while i < len
        invariant
            len == arr1.len(),
            len == arr2.len(),
            i <= len,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == (arr1[k] % arr2[k]),
            forall|k: int| 0 <= k < len ==> arr2[k] != 0,
            forall|k: int| 0 <= k < len ==> i32::MIN <= #[trigger] (arr1[k] % arr2[k]) <= i32::MAX,
        decreases len - i
    {
        let val = arr1[i] % arr2[i];
        result.push(val);
        i = i + 1;
    }

    result
}
// </vc-code>

} // verus!

fn main() {}