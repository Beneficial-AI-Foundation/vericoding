use vstd::prelude::*;

verus! {

//IMPL has_only_one_distinct_element
/* code modified by LLM (iteration 3): Fixed function structure by properly placing ensures clause in function signature and removing duplicate return statement */
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() == 0 {
        return true;
    }
    
    let first = arr[0];
    for i in 1..arr.len()
        invariant
            forall|j: int| 1 <= j < i ==> arr[0] == arr[j],
    {
        if arr[i] != first {
            return false;
        }
    }
    
    true
}

} // verus!

fn main() {}