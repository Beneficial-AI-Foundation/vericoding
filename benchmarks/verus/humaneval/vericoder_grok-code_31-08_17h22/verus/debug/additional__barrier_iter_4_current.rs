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
    let mut i = 1;
    while i < p + 1
        invariant
            1 <= i <= p + 1,
            forall |k: int| 0 <= k < i ==> arr@[k] <= max_left
    {
        if arr[i] > max_left {
            max_left = arr[i];
        }
        i += 1;
    }
    proof {
        assert forall |k: int| 0 <= k <= p implies arr@[k] <= max_left by {
            // invariant after loop: since i == p+1, forall k 0<=k<p+1 i.e. <=p
        };
    }
    let mut min_right = arr[p + 1];
    let mut j = p + 2;
    while j < arr.len()
        invariant
            p + 2 <= j <= arr.len(),
            forall |l: int| p + 1 <= l < j ==> min_right <= arr@[l]
    {
        if arr[j] < min_right {
            min_right = arr[j];
        }
        j += 1;
    }
    proof {
        assert forall |l: int| p + 1 <= l < arr.len() implies min_right <= arr@[l] by {
            // invariant after loop: since j == arr.len(), forall l p+1 <=l <arr.len()
        };
    }
    let result = max_left < min_right;
    if result {
        proof {
            assert forall |k: int, l: int| 0 <= k <= p && p < l < arr.len() implies arr@[k] < arr@[l] by {
                assert(forall |kk: int| 0 <= kk <= p ==> arr@[kk] <= max_left);
                assert(forall |ll: int| p < ll < arr.len() ==> min_right <= arr@[ll]);
                // hence arr@[k] <= max_left < min_right <= arr@[l]
            };
        }
    }
    return result;
}
// </vc-code>

fn main() {}
}