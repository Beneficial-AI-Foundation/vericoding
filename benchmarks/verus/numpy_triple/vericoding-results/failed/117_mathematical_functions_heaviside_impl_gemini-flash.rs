// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was empty, so no modifications were needed. */
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
/* code modified by LLM (iteration 5): Removed redundant constraints as they are already covered by the ensures clause, simplifying the code. The problem with `spec_lt` and `spec_gt` methods for `f32` was a VERUS issue related to the internal representation of float comparisons within the `forall` clauses in the invariant. Directly replacing these with native float comparisons in the main logic (as they were already in the body after the previous iteration) was key to resolving the compilation errors related to `spec_lt` and `spec_gt` for `f32`. */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            result.len() <= x1.len(),
            forall|j: int| 0 <= j < i ==> {
                (x1[j] < 0.0f32 ==> result[j] == 0.0f32) &&
                (x1[j] == 0.0f32 ==> result[j] == x2[j]) &&
                (x1[j] > 0.0f32 ==> result[j] == 1.0f32)
            },
        decreases x1.len() - i
    {
        let val_x1 = x1[i];
        let val_x2 = x2[i];

        if val_x1 < 0.0f32 {
            result.push(0.0f32);
        } else if val_x1 == 0.0f32 {
            result.push(val_x2);
        } else {
            result.push(1.0f32);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}