// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}