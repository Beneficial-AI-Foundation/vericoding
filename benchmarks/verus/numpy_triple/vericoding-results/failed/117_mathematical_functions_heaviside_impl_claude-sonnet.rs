// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate spec functions to fix compilation error */

fn exec_is_negative(x: f32) -> (b: bool)
    ensures b == is_negative(x)
{
    x < 0.0f32
}

fn exec_is_zero(x: f32) -> (b: bool)
    ensures b == is_zero(x)
{
    x == 0.0f32
}

fn exec_is_positive(x: f32) -> (b: bool)
    ensures b == is_positive(x)
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
    /* code modified by LLM (iteration 5): fixed compilation error by removing duplicate spec functions */
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (is_negative(x1[j]) ==> result[j] == 0.0f32) &&
                (is_zero(x1[j]) ==> result[j] == x2[j]) &&
                (is_positive(x1[j]) ==> result[j] == 1.0f32) &&
                (result[j] == 0.0f32 || result[j] == 1.0f32 || result[j] == x2[j])
            },
        decreases x1.len() - i,
    {
        let val = if exec_is_negative(x1[i]) {
            0.0f32
        } else if exec_is_zero(x1[i]) {
            x2[i]
        } else {
            1.0f32
        };
        
        proof {
            assert(is_negative(x1[i]) ==> val == 0.0f32);
            assert(is_zero(x1[i]) ==> val == x2[i]);
            assert(is_positive(x1[i]) ==> val == 1.0f32);
        }
        
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}