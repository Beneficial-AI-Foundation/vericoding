use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers
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
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    
    loop
        invariant
            0 <= low as int <= high as int <= arr.len() as int,
            forall|i: int| 0 <= i < low as int ==> #[trigger](arr@[i]) < target,
            forall|i: int| high as int <= i < arr.len() ==> #[trigger](arr@[i]) > target,
    {
        if !(low < high) {
            break;
        }
        let mid: usize = low + (high - low) / 2;
        if arr@[mid as int] < target {
            low = mid + 1;
        } else if arr@[mid as int] > target {
            high = mid;
        } else {
            return Some(mid);
        }
    }
    return None;
}
// </vc-code>

fn main() {}
}