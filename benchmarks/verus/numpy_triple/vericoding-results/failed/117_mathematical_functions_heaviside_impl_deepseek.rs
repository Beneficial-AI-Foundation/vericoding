// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_f32_zero_properties()
    ensures
        forall|x: f32| is_zero(x) == (x == 0.0f32),
        forall|x: f32| is_positive(x) == (x.spec_gt(0.0f32)),
        forall|x: f32| is_negative(x) == (x.spec_lt(0.0f32)),
{
}

proof fn lemma_f32_trichotomy()
    ensures
        forall|x: f32| is_zero(x) || is_positive(x) || is_negative(x),
        forall|x: f32| !(is_zero(x) && is_positive(x)),
        forall|x: f32| !(is_zero(x) && is_negative(x)),
        forall|x: f32| !(is_positive(x) && is_negative(x)),
{
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
    /* code modified by LLM (iteration 5): Fixed float comparison operators to use spec_lt/spec_gt methods */
    lemma_f32_zero_properties();
    lemma_f32_trichotomy();
    
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (x1[j].spec_lt(0.0f32) ==> result[j] == 0.0f32) &&
                (x1[j] == 0.0f32 ==> result[j] == x2[j]) &&
                (x1[j].spec_gt(0.0f32) ==> result[j] == 1.0f32) &&
                (result[j] == 0.0f32 || result[j] == 1.0f32 || result[j] == x2[j])
            }
        decreases n - i,
    {
        let x1_val = x1[i];
        let x2_val = x2[i];
        
        if x1_val.spec_lt(0.0f32) {
            result.push(0.0f32);
        } else if x1_val == 0.0f32 {
            result.push(x2_val);
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