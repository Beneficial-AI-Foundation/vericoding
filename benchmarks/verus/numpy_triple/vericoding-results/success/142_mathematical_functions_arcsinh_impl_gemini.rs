// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
exec fn arcsinh_f32(x: f32) -> (result: f32)
    ensures
        x == 0.0f32 ==> result == 0.0f32,
{
    x.asinh()
}
// </vc-helpers>

// <vc-spec>
fn numpy_arcsinh(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            /* Sanity check: arcsinh(0) = 0 */
            x@[i] == 0.0f32 ==> result@[i] == 0.0f32
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i as nat <= x@.len(),
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> (x@[j] == 0.0f32 ==> result@[j] == 0.0f32),
        decreases x.len() - i
    {
        let val = x[i];
        let sinh_val = arcsinh_f32(val);
        result.push(sinh_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}