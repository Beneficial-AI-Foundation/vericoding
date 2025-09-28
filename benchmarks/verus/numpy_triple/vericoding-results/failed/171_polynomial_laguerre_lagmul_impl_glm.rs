// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type issues and loop range */
fn multiply_polynomials(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
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
{
    let len1 = c1@.len() as int;
    let len2 = c2@.len() as int;
    let result_len = len1 + len2 - 1;
    let mut result = Vec::with_capacity(result_len as usize);
    
    for i in 0..result_len
        invariant 
            0 <= i <= result_len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (result@[j] != 0.0 ==> 
                    exists|k: int, l: int| 
                        0 <= k < len1 && 
                        0 <= l < len2 && 
                        k + l == j && 
                        c1@[k] != 0.0 && 
                        c2@[l] != 0.0)
        decreases result_len - i
    {
        let mut sum = 0.0;
        let mut found_nonzero = false;
        
        for j in 0..i+1
            invariant 
                0 <= j <= i + 1,
                forall|k: int| 0 <= k < j ==> 
                    (i - k >= 0 && i - k < len2 && k < len1 ==> 
                        (sum != 0.0 ==> found_nonzero) &&
                        (c1@[k] != 0.0 && c2@[i - k] != 0.0 ==> found_nonzero))
            decreases i + 1 - j
        {
            if j < len1 && (i - j) < len2 && (i - j) >= 0 {
                let product = c1@[j] * c2@[i - j];
                sum = sum + product;
                if c1@[j] != 0.0 && c2@[i - j] != 0.0 {
                    found_nonzero = true;
                }
            }
        }
        
        result.push(sum);
    }
    
    result
}
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
/* code modified by LLM (iteration 5): no changes made */
{
    let result = multiply_polynomials(c1, c2);
    result
}
// </vc-code>

}
fn main() {}