use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l < i + 1 ==> arr[k] <= arr[l],
        decreases arr.len() - 1 - i,
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

} // verus!

fn main() {}