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
    /* code modified by LLM (iteration 4): Added a decreases clause to the while loop to prove termination. */
    let mut i: usize = 0;

    if arr.len() <= 1 {
        return true;
    }

    while i < arr.len() - 1
        invariant
            0 <= i < arr.len(),
            forall|k: int, l: int| 0 <= k < l <= i as int ==> arr[k] <= arr[l],
        decreases arr.len() - 1 - i,
    {
        if arr[i] > arr[i+1] {
            proof {
                let k = i as int;
                let j = (i + 1) as int;
                assert(arr[k] > arr[j]);
                assert(exists|a: int, b: int| 0 <= a < b < arr.len() && arr[a] > arr[b]);
            }
            return false;
        }
        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}