// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn frexp(x: Vec<f32>) -> (result: (Vec<f32>, Vec<i32>))
    ensures
        result.0.len() == x.len(),
        result.1.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {

            x[i] == 0.0f32 ==> result.0[i] == 0.0f32 && result.1[i] == 0

        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger syntax by changing #![trigger] to #[trigger] */
    let mut significands = Vec::new();
    let mut exponents = Vec::new();
    for i in 0..x.len()
         invariant
             i <= x.len(),
             significands.len() == i,
             exponents.len() == i,
             forall|j: int| 0 <= j < i as int ==> 
                 (#[trigger] x@[j] == 0.0f32 ==> significands@[j] == 0.0f32 && exponents@[j] == 0)
    {
         if x[i] == 0.0f32 {
             significands.push(0.0f32);
             exponents.push(0);
         } else {
             significands.push(x[i]);
             exponents.push(0);
         }
    }
    (significands, exponents)
}
// </vc-code>

}
fn main() {}