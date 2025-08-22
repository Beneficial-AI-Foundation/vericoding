use vstd::prelude::*;

fn main() {}

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() == 0 {
        return true;
    }
    
    let first = arr[0];
    for j in 1..arr.len()
        invariant
            forall|i: int| 1 <= i < j ==> first == arr[i],
    {
        if arr[j] != first {
            return false;
        }
    }
    true
}

} // verus!