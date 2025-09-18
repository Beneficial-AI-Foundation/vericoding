// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixing spec function to avoid spec_add/spec_mul errors */
spec fn hermite_polynomial(coef: Seq<f32>, x: f32, i: nat) -> f32
    decreases coef.len() - i
{
    if i >= coef.len() {
        0.0
    } else if i == coef.len() - 1 {
        coef[i as int]
    } else if i == coef.len() - 2 {
        coef[i as int] + 2.0 * x * coef[(i + 1) as int]
    } else {
        coef[i as int] + 2.0 * x * hermite_polynomial(coef, x, i + 1) - 2.0 * ((i + 1) as f32) * hermite_polynomial(coef, x, i + 2)
    }
}
// </vc-helpers>

// <vc-spec>
fn hermite_eval(coef: Vec<f32>, x: f32) -> (result: f32)
    requires coef.len() > 0,
    ensures 
        coef.len() == 1 ==> result == coef[0],
        coef.len() >= 2 ==> true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementing Hermite polynomial evaluation using backward recurrence */
    let n = coef.len();
    if n == 1 {
        return coef[0];
    }
    
    let mut p_prev: f32 = 0.0;
    let mut p_curr: f32 = coef[(n - 1) as usize];
    
    let mut i: usize = n - 2;
    loop
        invariant
            i < n,
            n >= 2,
            coef.len() == n,
        decreases i
    {
        let p_next = coef[i] + 2.0 * x * p_curr - 2.0 * ((i + 1) as f32) * p_prev;
        p_prev = p_curr;
        p_curr = p_next;
        
        if i == 0 {
            break;
        }
        i = i - 1;
    }
    
    p_curr
}
// </vc-code>

}
fn main() {}