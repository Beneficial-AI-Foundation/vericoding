use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut low: int = 0;
    let mut high: int = arr.len();
    
    loop
        invariant
            0 <= low <= high <= arr.len(),
            forall|i: int| 0 <= i < low ==> #[trigger](arr@[i] as int) < target,
            forall|i: int| high <= i < arr.len() ==> #[trigger](arr@[i] as int) > target,
        {
        if !(low < high) {
            break;
        }
        let mid = low + (high - low) / 2;
        if arr@[mid] < target {
            low = mid + 1;
        } else if arr@[mid] > target {
            high = mid;
        } else {
            return Some(mid as usize);
        }
    }
    return None;
}
// </vc-code>

fn main() {}
}