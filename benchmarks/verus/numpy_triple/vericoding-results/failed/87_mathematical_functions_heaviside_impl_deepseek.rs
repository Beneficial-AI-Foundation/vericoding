// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed conflicting spec definitions */
// </vc-helpers>

// <vc-spec>
spec fn is_zero(x: f32) -> bool {
    true
}

spec fn is_positive(x: f32) -> bool {
    true
}

spec fn is_negative(x: f32) -> bool {
    true
}

fn heaviside(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> {
            (is_negative(x1[i]) ==> result[i] == 0.0f32) &&
            (is_zero(x1[i]) ==> result[i] == x2[i]) &&
            (is_positive(x1[i]) ==> result[i] == 1.0f32) &&
            (result[i] == 0.0f32 || result[i] == 1.0f32 || result[i] == x2[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented main function body */
{
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (is_negative(x1@[j]) ==> result@[j] == 0.0f32) &&
                (is_zero(x1@[j]) ==> result@[j] == x2@[j]) &&
                (is_positive(x1@[j]) ==> result@[j] == 1.0f32) &&
                (result@[j] == 0.0f32 || result@[j] == 1.0f32 || result@[j] == x2@[j])
            }
    {
        let x1_val = x1[i];
        let x2_val = x2[i];
        let res_val = if x1_val < 0.0f32 {
            0.0f32
        } else if x1_val == 0.0f32 {
            x2_val
        } else {
            1.0f32
        };
        result.push(res_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}