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
    /* code modified by LLM (iteration 5): Fixed casting issues by using usize directly */
    let n = c.len();
    let mut result: Vec<f32> = Vec::new();
    
    if n == 1 {
        result.push(c[0]);
        return result;
    }
    
    // Initialize result with zeros
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: usize| j < i ==> result@[j as int] == 0.0f32,
    {
        result.push(0.0f32);
        i = i + 1;
    }
    
    // L_0(x) = c[0]
    result.set(0, c[0]);
    
    if n == 1 {
        return result;
    }
    
    // L_1(x) = c[0] + c[1]*(1-x)
    result.set(0, c[0] + c[1]);
    result.set(1, -c[1]);
    
    // Compute higher order terms using recurrence relation
    let mut k: usize = 2;
    while k < n
        invariant
            2 <= k <= n,
            result.len() == n,
    {
        // L_k(x) = ((2k-1-x)*L_{k-1}(x) - (k-1)*L_{k-2}(x))/k
        let mut temp: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                temp.len() == j,
        {
            temp.push(0.0f32);
            j = j + 1;
        }
        
        // Multiply L_{k-1} by (2k-1-x)
        let factor = (2 * k - 1) as f32;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                temp.len() == n,
        {
            if i == 0 {
                temp.set(i, result[i] * factor);
            } else {
                let val = result[i] * factor;
                if i > 0 {
                    temp.set(i, val - result[i - 1]);
                }
            }
            i = i + 1;
        }
        
        // Subtract (k-1)*L_{k-2}
        if k >= 2 {
            let k_minus_one = (k - 1) as f32;
            let mut i: usize = 0;
            while i < n - 1
                invariant
                    i <= n - 1,
                    temp.len() == n,
            {
                temp.set(i, temp[i] - result[i] * k_minus_one);
                i = i + 1;
            }
        }
        
        // Divide by k and multiply by c[k]
        let k_float = k as f32;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                result.len() == n,
                temp.len() == n,
        {
            result.set(i, result[i] + temp[i] * c[k] / k_float);
            i = i + 1;
        }
        
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}