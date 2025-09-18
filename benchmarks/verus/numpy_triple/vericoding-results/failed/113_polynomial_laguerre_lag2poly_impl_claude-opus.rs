// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial(c: Seq<f32>, x: f32) -> f32;

spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lag2poly(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),

        forall|x: f32| evaluate_polynomial(result@, x) == evaluate_laguerre_polynomial(c@, x),

        c.len() == 1 ==> result@ == c@,

        c.len() > 0 ==> evaluate_polynomial(result@, 0.0) == evaluate_laguerre_polynomial(c@, 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using Vec::new and push instead of vec! macro */
    let mut result = Vec::new();
    
    if c.len() == 1 {
        result.push(c[0]);
        return result;
    }
    
    // Initialize result vector with the same length as c
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.len() == i,
        decreases c.len() - i
    {
        result.push(0.0);
        i = i + 1;
    }
    
    // Copy values from c to result
    let mut j: usize = 0;
    while j < c.len()
        invariant
            j <= c.len(),
            result.len() == c.len(),
        decreases c.len() - j
    {
        result.set(j, c[j]);
        j = j + 1;
    }
    
    proof {
        assert(result.len() == c.len());
        if c.len() == 1 {
            assert(result@ == c@);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}