use vstd::prelude::*;

fn main() {
    // Simple demonstration of the functions
    let vec1 = vec![1, 2, 3, 4];
    let vec2 = vec![3, 4, 5, 6];
    let shared = shared_elements(&vec1, &vec2);
    println!("Shared elements: {:?}", shared);
}

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