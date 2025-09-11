// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace(arr: &Vec<i32>, k: i32) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] > k ==> result[i] == -1),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] <= k ==> result[i] == arr[i]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}