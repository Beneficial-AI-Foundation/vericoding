use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
    return None;  // TODO: Remove this line and implement the function body
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut index = 0;
    while index < arr.len() {
        if arr[index] == target {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!
