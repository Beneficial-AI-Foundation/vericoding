// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn equal_length<T>(v1: Vec<T>, v2: Vec<T>) -> bool { v1.len() == v2.len() }
// </vc-helpers>

// <vc-spec>
fn asmatrix(data: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
{
    data
}
// </vc-code>

}
fn main() {}