// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn copy(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}