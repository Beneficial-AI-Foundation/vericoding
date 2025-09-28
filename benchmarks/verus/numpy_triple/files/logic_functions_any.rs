// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32) &&
        (v@.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}