use vstd::prelude::*;

verus! {

// <vc-helpers>
/* No helpers needed */
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
    let mut lo: usize = 0;
    let mut hi: usize = arr.len();

    while lo < hi
        invariant
            lo <= hi && hi <= arr.len(),
            forall|i: int| 0 <= i && i < (lo as int) ==> #[trigger] arr[i] < target,
            forall|i: int| (hi as int) <= i && i < (arr.len() as int) ==> #[trigger] arr[i] > target
    {
        let mid: usize = (lo + hi) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    if lo < arr.len() && arr[lo] == target {
        Some(lo)
    } else {
        None
    }
}
// </vc-code>

fn main() {}
}