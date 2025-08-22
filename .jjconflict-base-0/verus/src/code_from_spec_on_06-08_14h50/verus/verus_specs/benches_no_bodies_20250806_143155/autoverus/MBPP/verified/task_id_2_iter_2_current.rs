use vstd::prelude::*;

fn main() {
}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < list1.len()
        invariant
            forall|k: int|
                0 <= k < result.len() ==> (list1@.contains(#[trigger] result[k]) && list2@.contains(
                    #[trigger] result[k],
                )),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases list1.len() - i
    {
        let elem = list1[i];
        if contains(list2, elem) && !contains(&result, elem) {
            result.push(elem);
        }
        i += 1;
    }
    
    result
}

} // verus!