// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_finite_f32(x: f32) -> bool;
spec fn is_infinite_f32(x: f32) -> bool;
spec fn is_nan_f32(x: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn isfinite(x: Vec<f32>) -> (result: Vec<bool>)
    requires x@.len() > 0,
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (result@[i] == (!is_infinite_f32(x@[i]) && !is_nan_f32(x@[i])))
            &&& (result@[i] == true <==> is_finite_f32(x@[i]))
            &&& (result@[i] == false <==> (is_nan_f32(x@[i]) || is_infinite_f32(x@[i])))
            &&& (x@[i] == 0.0f32 ==> result@[i] == true)
            &&& (result@[i] == false ==> (is_nan_f32(x@[i]) || is_infinite_f32(x@[i])))
            &&& (result@[i] == true ==> !is_nan_f32(x@[i]) && !is_infinite_f32(x@[i]))
        }
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