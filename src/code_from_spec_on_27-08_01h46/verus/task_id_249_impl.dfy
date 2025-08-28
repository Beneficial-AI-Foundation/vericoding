use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    // impl-start
    let mut i = 0;
    while i < arr.len()
        // invariants-start
        invariant
            0 <= i <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
        decreases arr.len() - i
        // invariants-end
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
    // impl-end
}

fn vec_contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == arr@.contains(key),
{
    let ghost original_seq = arr@;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            arr@ == original_seq,
            forall|j: int| 0 <= j < i ==> arr@[j] != key,
        decreases arr.len() - i
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < result.len() ==> (arr1@.contains(result@[k]) && arr2@.contains(result@[k])),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result@[k1] != result@[k2],
        decreases arr1.len() - i
    {
        let val = arr1[i];
        if vec_contains(arr2, val) && !vec_contains(&result, val) {
            result.push(val);
        }
        i += 1;
    }
    
    result
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}