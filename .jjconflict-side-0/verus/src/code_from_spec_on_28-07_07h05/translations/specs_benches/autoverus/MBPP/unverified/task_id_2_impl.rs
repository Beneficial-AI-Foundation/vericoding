use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
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
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut result = Vec::new();
    
    for i in 0..list1.len()
        invariant
            forall|k: int|
                0 <= k < result.len() ==> (list1@.contains(#[trigger] result[k]) && list2@.contains(
                    #[trigger] result[k],
                )),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        let elem = list1[i];
        if contains(list2, elem) && !contains(&result, elem) {
            result.push(elem);
        }
    }
    
    result
}

} // verus!