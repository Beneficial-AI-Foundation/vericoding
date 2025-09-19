// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagdiv(c1: Vec<f64>, c2: Vec<f64>) -> (result: (Vec<f64>, Vec<f64>))
    requires 
        c1@.len() > 0,
        c2@.len() > 0,
        exists|i: int| 0 <= i < c2@.len() && c2[i] != 0.0,
    ensures
        result.0@.len() == c1@.len(),
        result.1@.len() == c2@.len(),
        c2@.len() > 0 ==> exists|highest_nonzero: int| 
            0 <= highest_nonzero < c2@.len() &&
            (forall|j: int| highest_nonzero < j < result.1@.len() ==> result.1[j] == 0.0) &&
            c2[highest_nonzero] != 0.0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}