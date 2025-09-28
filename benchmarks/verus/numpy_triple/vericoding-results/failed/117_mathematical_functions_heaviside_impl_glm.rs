// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): removed helper functions and used explicit conditions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                ((x1[j] < 0.0f32) ==> result[j] == 0.0f32) &&
                ((x1[j] == 0.0f32) ==> result[j] == x2[j]) &&
                ((x1[j] > 0.0f32) ==> result[j] == 1.0f32)
            }
        decreases x1.len() - i
    {
        if x1[i] < 0.0f32 {
            result.push(0.0f32);
        } else if x1[i] == 0.0f32 {
            assert(i < x2.len()) by {
                assert(x1.len() == x2.len());
                assert(i < x1.len());
            };
            result.push(x2[i]);
        } else {
            result.push(1.0f32);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}