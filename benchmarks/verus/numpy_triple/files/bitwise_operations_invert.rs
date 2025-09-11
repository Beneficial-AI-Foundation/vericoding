// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}