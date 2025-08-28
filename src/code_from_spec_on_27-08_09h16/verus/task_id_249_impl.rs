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
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
        // invariants-end
        decreases arr.len() - i
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
    // impl-end
}

fn result_contains(result: &Vec<i32>, key: i32) -> (found: bool)
    ensures
        found == (exists|i: int| 0 <= i < result.len() && result[i] == key)
{
    let mut i = 0;
    while i < result.len()
        invariant
            forall|m: int| 0 <= m < i ==> result[m] != key
        decreases result.len() - i
    {
        if result[i] == key {
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
            forall|k: int| 0 <= k < result.len() ==> (arr1@.contains(result[k]) && arr2@.contains(result[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases arr1.len() - i
    {
        let val = arr1[i];
        if contains(arr2, val) && !result_contains(&result, val) {
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