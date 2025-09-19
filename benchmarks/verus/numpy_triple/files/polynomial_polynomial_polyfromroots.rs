// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyfromroots(roots: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result@.len() == roots@.len() + 1,
        result@[result@.len() - 1] == 1.0
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