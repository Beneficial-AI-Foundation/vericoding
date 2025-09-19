// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn take(arr: Vec<f32>, indices: Vec<usize>) -> (result: Vec<f32>)
    requires
        forall|i: int| 0 <= i < indices@.len() ==> indices[i] < arr@.len(),
    ensures
        result@.len() == indices@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> result[i] == arr[indices[i] as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}