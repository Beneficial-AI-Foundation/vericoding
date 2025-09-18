// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed requires clause and integer arithmetic */
spec fn valid_polynomial_multiplication(c1: Vec<f64>, c2: Vec<f64>, result: Vec<f64>) -> bool {
    result.len() == c1.len() + c2.len() - 1 &&
    forall|i: int| 0 <= i < result.len() ==> 
        (result[i] != 0.0 ==> 
            exists|j: int, k: int| 
                0 <= j < c1.len() && 
                0 <= k < c2.len() && 
                j + k == i && 
                c1[j] != 0.0 && 
                c2[k] != 0.0)
}

fn compute_coeff(c1: &Vec<f64>, c2: &Vec<f64>, i: usize) -> f64 
    requires c1.len() > 0 && c2.len() > 0 && i < c1.len() + c2.len() - 1
{
    let mut sum = 0.0;
    let mut j = 0;
    while j <= i && j < c1.len()
        invariant 0 <= j <= i + 1, j <= c1.len()
        decreases c1.len() - j
    {
        if i >= j {
            let k = i - j;
            if k < c2.len() {
                sum += c1@[j] * c2@[k];
            }
        }
        j += 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1.len() > 0 && c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1.len() && 
                    0 <= k < c2.len() && 
                    j + k == i && 
                    c1[j] != 0.0 && 
                    c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and precondition */
    if c1.len() == 0 || c2.len() == 0 {
        return Vec::new();
    }
    
    if c1.len() > usize::MAX / 2 || c2.len() > usize::MAX / 2 {
        return Vec::new();
    }
    
    let sum_len = c1.len() + c2.len();
    if sum_len == 0 {
        return Vec::new();
    }
    
    let result_len = sum_len - 1;
    let mut result = Vec::with_capacity(result_len);
    
    let mut i = 0;
    while i < result_len
        invariant 0 <= i <= result_len, result.len() == i, result_len == c1.len() + c2.len() - 1
        decreases result_len - i
    {
        let coeff = compute_coeff(&c1, &c2, i);
        result.push(coeff);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}