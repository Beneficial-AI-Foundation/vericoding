// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): chooser for heaviside value */
fn choose_heaviside_val(x: f32, y: f32) -> f32 { if x < 0.0f32 { 0.0f32 } else if x == 0.0f32 { y } else { 1.0f32 } }
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
    /* code modified by LLM (iteration 5): iterate using int indices with comma-separated invariants and build result */
    let mut result: Vec<f32> = Vec::new();
    let n: int = x1.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n,
        invariant result.len() == i as usize,
        decreases n - i
    {
        let xi: f32 = x1[i as usize];
        let yi: f32 = x2[i as usize];
        let vi: f32 = choose_heaviside_val(xi, yi);
        result.push(vi);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}