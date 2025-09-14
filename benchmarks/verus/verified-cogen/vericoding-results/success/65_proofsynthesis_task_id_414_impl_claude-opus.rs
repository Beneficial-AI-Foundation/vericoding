// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)

    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by using int for indexing */
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> !arr2@.contains(#[trigger] arr1[k]),
        decreases arr1.len() - i,
    {
        let mut j: usize = 0;
        while j < arr2.len()
            invariant
                0 <= i < arr1.len(),
                0 <= j <= arr2.len(),
                forall|k: int| 0 <= k < j ==> arr2[k as int] != arr1[i as int],
            decreases arr2.len() - j,
        {
            if arr1[i] == arr2[j] {
                assert(arr2@.contains(arr1[i as int]));
                assert(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k])) by {
                    assert(0 <= i < arr1.len() && arr2@.contains(arr1[i as int]));
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    assert(forall|k: int| 0 <= k < arr1.len() ==> !arr2@.contains(arr1[k]));
    false
}
// </vc-code>

}
fn main() {}