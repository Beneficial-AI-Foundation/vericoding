// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ndindex(shape: (usize, usize)) -> (indices: Vec<(usize, usize)>)
    requires shape.0 > 0 && shape.1 > 0,
    ensures 
        indices.len() == shape.0 * shape.1,
        forall|k: int| 0 <= k < indices.len() ==> {
            let (i, j) = indices[k];
            i < shape.0 && j < shape.1
        },
        forall|i: usize, j: usize| i < shape.0 && j < shape.1 ==> {
            exists|k: int| 0 <= k < indices.len() && indices[k] == (i, j)
        },
        forall|k: int| 0 <= k < indices.len() ==> {
            let (i, j) = indices[k];
            k == i * shape.1 + j
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}