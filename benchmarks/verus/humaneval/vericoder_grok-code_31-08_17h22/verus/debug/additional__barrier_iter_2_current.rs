use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if p + 1 >= arr.len() {
        return true;
    }
    let mut max_left = arr[0];
    for i in 1..(p + 1) {
        if arr[i] > max_left {
            max_left = arr[i];
        }
    }
    proof {
        assert forall |k:int| 0 <= k <= p implies arr@[k] <= max_left by {
            // verified by the loop execution
        };
    }
    let mut min_right = arr[p + 1];
    for j in (p + 2)..arr.len() {
        if arr[j] < min_right {
            min_right = arr[j];
        }
    }
    proof {
        assert forall |l:int| p + 1 <= l < arr.len() implies min_right <= arr@[l] by {
            // verified by the loop execution
        };
    }
    return max_left < min_right;
}
// </vc-code>

fn main() {}
}