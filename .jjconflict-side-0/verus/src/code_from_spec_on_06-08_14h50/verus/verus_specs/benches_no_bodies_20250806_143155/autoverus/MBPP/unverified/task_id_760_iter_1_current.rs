use vstd::prelude::*;

fn main() {}

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() <= 1 {
        return true;
    }
    
    let first = arr[0];
    for idx in 1..arr.len()
        invariant
            forall|j: int| 1 <= j < idx ==> arr[0] == arr[j]
    {
        if arr[idx] != first {
            return false;
        }
    }
    
    true
}

} // verus!