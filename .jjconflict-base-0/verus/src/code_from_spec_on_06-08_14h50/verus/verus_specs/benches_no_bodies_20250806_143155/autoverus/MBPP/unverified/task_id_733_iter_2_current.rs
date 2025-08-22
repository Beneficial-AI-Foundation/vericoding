use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
            idx < arr.len() && arr[idx as int] == target && 
            forall|k: int| 0 <= k < idx ==> arr[k] != target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> arr[k] != target,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
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