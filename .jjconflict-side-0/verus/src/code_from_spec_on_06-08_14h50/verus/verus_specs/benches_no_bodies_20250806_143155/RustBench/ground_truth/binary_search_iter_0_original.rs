use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        match result {
    return None;  // TODO: Remove this line and implement the function body
        },
{
    let mut low = 0;
    let mut high = arr.len();
    while low < high
        invariant
            low <= high && high <= arr.len(),
            forall|i: int| 0 <= i && i < low ==> arr[i] < target,
            forall|i: int| high <= i && i < arr.len() ==> arr[i] > target,
    {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid;
        } else {
            high = mid;
        }
    }
    None
}

fn main() {}
}
