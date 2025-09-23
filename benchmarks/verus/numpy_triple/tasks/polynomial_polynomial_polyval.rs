// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyval(x: Vec<f64>, c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x@.len() > 0,
        c@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            #[trigger] result@[i] == result@[i] &&
            (c@.len() == 1 ==> result@[i] == c@[0]) &&
            (forall|j: int| 0 <= j < c@.len() && c@[j] == 0.0 ==> #[trigger] result@[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}