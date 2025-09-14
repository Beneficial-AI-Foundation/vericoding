// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sorted(arr: &Vec<i32>) -> (result: bool)

    requires
        arr.len() > 0,

    ensures
        result == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    if arr.len() == 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            i < arr.len(),
            forall|k: int, l: int| 0 <= k < l <= i ==> arr@[k] <= arr@[l],
        decreases arr.len() - 1 - i,
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr@[k] <= arr@[l] by {
            if l <= i {
                // Already covered by loop invariant
            } else {
                assert(l == i + 1);
                if k < i {
                    // k < i < l, so arr@[k] <= arr@[i] by invariant
                    // and arr@[i] <= arr@[l] since we checked it
                } else {
                    assert(k == i);
                    // We directly checked arr@[i] <= arr@[i+1]
                }
            }
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}