// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn laggrid2d(x: Vec<f64>, y: Vec<f64>, c: Vec<Vec<f64>>) -> (result: Vec<Vec<f64>>)
    requires
        c@.len() > 0,
        c@.len() > 0 ==> c@[0].len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() == c@[0].len(),
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == y@.len(),
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