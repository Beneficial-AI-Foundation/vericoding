// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove duplicate spec function definitions */
fn is_negative_exec(x: f32) -> (result: bool)
    ensures result == is_negative(x)
{
    x < 0.0f32
}

fn is_zero_exec(x: f32) -> (result: bool)
    ensures result == is_zero(x)
{
    x == 0.0f32
}

fn is_positive_exec(x: f32) -> (result: bool)
    ensures result == is_positive(x)
{
    x > 0.0f32
}
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
    /* code modified by LLM (iteration 5): Use proper conditional logic with exec helpers */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (is_negative(x1[j]) ==> result[j] == 0.0f32) &&
                (is_zero(x1[j]) ==> result[j] == x2[j]) &&
                (is_positive(x1[j]) ==> result[j] == 1.0f32) &&
                (result[j] == 0.0f32 || result[j] == 1.0f32 || result[j] == x2[j])
            },
        decreases x1.len() - i
    {
        let val = if is_negative_exec(x1[i]) {
            0.0f32
        } else if is_zero_exec(x1[i]) {
            x2[i]
        } else {
            assert(is_positive_exec(x1[i]));
            1.0f32
        };
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}