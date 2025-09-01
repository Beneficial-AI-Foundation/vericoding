use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    // impl-start
    let mut i = 0;
    while i <= p
        invariant
            0 <= i <= p + 1,
            forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k] < arr[l],
    {
        let mut j = p + 1;
        while j < arr.len()
            invariant
                p + 1 <= j <= arr.len(),
                forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k] < arr[l],
                forall|l: int| p < l < j ==> arr[i] < arr[l],
        {
            if arr[i] >= arr[j] {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
    // impl-end
}
// </vc-code>

fn main() {}
}