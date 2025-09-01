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
    let mut low = 0;
    let mut high = arr.len() - 1;
    while low <= high {
        invariant: {
            0 <= low &&
            high < arr.len() &&
            (forall|i: int| 0 <= i && i < low ==> arr[i] != target) &&
            (forall|i: int| high < i && i < arr.len() ==> arr[i] != target)
        }
        let mid = (low + high) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            assert(forall|i: int|
                low <= i && i <= mid
                ==> #[trigger] arr[i] < target
            );
            low = mid + 1;
        } else {
            assert(forall|i: int|
                mid <= i && i <= high
                ==> #[trigger] arr[i] > target
            );
            high = mid - 1;
        }
    }
    return None;
}
// </vc-code>

fn main() {}
}