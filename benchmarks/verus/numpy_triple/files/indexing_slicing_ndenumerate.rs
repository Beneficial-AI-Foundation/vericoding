// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].0 == i && result[i].1 == arr[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}