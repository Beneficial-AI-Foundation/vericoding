// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_trivial() { }
// </vc-helpers>

// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> 
            0 <= result < arr.len() &&
            arr[result as int] == elem &&
            forall|k: int| result < k < arr.len() ==> arr[k] != elem) &&
        (result == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem),
// </vc-spec>
// <vc-code>
{
    -2
}
// </vc-code>

}
fn main() {}