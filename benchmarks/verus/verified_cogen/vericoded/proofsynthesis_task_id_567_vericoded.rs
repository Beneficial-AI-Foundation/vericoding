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
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l < i + 1 ==> arr[k] <= arr[l],
        decreases arr.len() - 1 - i
    {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}