use vstd::prelude::*;

fn main() {
    // Main function - can remain empty for this example
}

verus! {

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
            idx < arr.len() && 
            arr[idx as int] == target &&
            forall|k: int| 0 <= k < idx ==> arr[k] != target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut index = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> arr[k] != target,
            index <= arr.len(),
        decreases arr.len() - index
    {
        if arr[index] == target {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!