use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
/* No helpers needed */
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut lo: int = 0;
    let mut hi: int = arr.len();

    while lo < hi
        invariant
            0 <= lo && lo <= hi && hi <= arr.len(),
            forall|i: int| 0 <= i && i < lo ==> #[trigger] arr@[i] < target,
            forall|i: int| hi <= i && i < arr.len() ==> #[trigger] arr@[i] > target
    {
        let mid: int = (lo + hi) / 2;
        // mid is in [lo, hi)
        if arr@[mid] == target {
            return Some(mid as usize);
        } else if arr@[mid] < target {
            // arr[mid] < target => all i < mid+1 have arr[i] < target
            // update lo to mid+1
            lo = mid + 1;
        } else {
            // arr[mid] > target
            hi = mid;
        }
    }

    if lo < arr.len() && arr@[lo] == target {
        Some(lo as usize)
    } else {
        None
    }
    // impl-end
}
// </vc-code>

fn main() {}
}