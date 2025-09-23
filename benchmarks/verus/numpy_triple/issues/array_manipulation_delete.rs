// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn delete(arr: Vec<f32>, index: usize) -> (result: Vec<f32>)
    requires 
        arr.len() > 0,
        index < arr.len(),
    ensures 
        result.len() == arr.len() - 1,
        forall|i: int| 0 <= i < index ==> result[i] == arr[i],
        forall|i: int| index <= i < result.len() ==> result[i] == arr[i + 1],
        forall|i: int| 0 <= i < arr.len() && i != index ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == arr[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}