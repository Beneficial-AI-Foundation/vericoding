use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty as no additional helpers needed for this implementation
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
    if arr.len() == 0 {
        return None;
    }
    let mut low: usize = 0;
    let mut high = arr.len() - 1;
    while low <= high
        invariant(
            arr.len() > 0,
            0 <= low <= high < arr.len(),
            forall|i: int| #[trigger(arr@[i])] 0 <= i < arr.len() && !(low as int <= i as int <= high as int) ==> arr@[i] != target,
        )
    {
        let mid = low + (high - low) / 2;
        assert(0 <= low <= mid <= high < arr.len());
        proof {
            assert(low as int <= mid as int <= high as int);
        }
        if arr@[mid] == target {
            return Some(mid);
        } else if arr@[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    None
    // impl-end
}
// </vc-code>

fn main() {}
}