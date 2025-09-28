// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1@.len() > 0 && c2@.len() > 0,
    ensures 
        result@.len() == c1@.len() + c2@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1@.len() && 
                    0 <= k < c2@.len() && 
                    j + k == i && 
                    c1@[j] != 0.0 && 
                    c2@[k] != 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix bounds checking and empty input handling */
    let c1_len = c1.len();
    let c2_len = c2.len();
    
    let result_len = c1_len + c2_len - 1;
    let mut result: Vec<f64> = Vec::new();
    
    let mut i = 0;
    while i < result_len
        invariant
            result@.len() == i,
            i <= result_len,
            result_len == c1@.len() + c2@.len() - 1,
            c1@.len() > 0,
            c2@.len() > 0,
            c1_len == c1@.len(),
            c2_len == c2@.len(),
        decreases result_len - i
    {
        let mut sum = 0.0;
        let mut j = 0;
        
        while j < c1_len
            invariant
                j <= c1_len,
                i < result_len,
                result_len == c1@.len() + c2@.len() - 1,
                c1@.len() > 0,
                c2@.len() > 0,
                c1_len == c1@.len(),
                c2_len == c2@.len(),
                i >= 0,
                j >= 0,
            decreases c1_len - j
        {
            if i >= j {
                let k = i - j;
                if k < c2_len {
                    assert(j < c1@.len());
                    assert(k < c2@.len());
                    sum = sum + c1[j] * c2[k];
                }
            }
            j = j + 1;
        }
        
        result.push(sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}