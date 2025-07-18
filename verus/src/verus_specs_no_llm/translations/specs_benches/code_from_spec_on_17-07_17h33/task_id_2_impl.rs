use vstd::prelude::*;

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    /* code modified by LLM (iteration 2): Added decreases clause to prove termination */
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] != key,
        decreases arr.len() - i
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
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
    /* code modified by LLM (iteration 2): Added decreases clause to prove termination */
    let mut shared = Vec::new();
    let mut i = 0;
    
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int| 0 <= k < shared.len() ==> (list1@.contains(shared[k]) && list2@.contains(shared[k])),
            forall|k1: int, k2: int| 0 <= k1 < k2 < shared.len() ==> shared[k1] != shared[k2],
        decreases list1.len() - i
    {
        let element = list1[i];
        if contains(list2, element) && !contains(&shared, element) {
            shared.push(element);
        }
        i += 1;
    }
    
    shared
}

} // verus!

fn main() {}