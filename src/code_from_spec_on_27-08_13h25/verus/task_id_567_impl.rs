use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this case
// </vc-helpers>

// <vc-spec>
fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut is_sorted = true;
    let mut i: usize = 0;
    
    while i < arr.len() - 1
        invariant
            0 <= i < arr.len(),
            is_sorted ==> (forall|k: int, l: int| 0 <= k < l <= i as int ==> arr[k] <= arr[l]),
        decreases arr.len() - i
    {
        if arr[i] > arr[i + 1] {
            is_sorted = false;
            break;
        }
        i = i + 1;
    }
    
    // Add a proof to handle the case when loop exits without breaking
    proof {
        if is_sorted && i == arr.len() - 1 {
            assert(forall|k: int, l: int| 0 <= k < l < arr.len() ==> {
                if l <= i as int {
                    arr[k] <= arr[l]
                } else {
                    arr[k] <= arr[l]
                }
            });
        }
    }
    
    is_sorted
}
// </vc-code>

} // verus!

fn main() {}