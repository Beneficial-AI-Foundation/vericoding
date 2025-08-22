use vstd::prelude::*;

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
    {
        if arr[i] == key {
            return true;
        }
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    // post-conditions-end
{
    let mut result = Vec::new();
    
    for i in 0..list1.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> (list1@.contains(result[k]) && list2@.contains(result[k])),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
    {
        let elem = list1[i];
        if contains(list2, elem) && !contains(&result, elem) {
            result.push(elem);
        }
    }
    
    result
}

} // verus!

fn main() {}