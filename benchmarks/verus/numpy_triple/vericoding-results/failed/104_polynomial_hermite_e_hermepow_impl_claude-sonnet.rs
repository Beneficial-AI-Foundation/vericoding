// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed saturating_sub to regular subtraction on usize */
spec fn poly_mult_len(len1: usize, len2: usize) -> usize {
    if len1 == 0 || len2 == 0 { 0 } else { len1 + len2 - 1 }
}

fn poly_multiply(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires a.len() > 0, b.len() > 0
    ensures result.len() == a.len() + b.len() - 1
{
    let mut result = vec![0.0; a.len() + b.len() - 1];
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == a.len() + b.len() - 1
    {
        let mut j = 0;
        while j < b.len()
            invariant
                i < a.len(),
                j <= b.len(),
                result.len() == a.len() + b.len() - 1
        {
            result.set(i + j, result[i + j] + a[i] * b[j]);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| #![trigger result[i]] 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| #![trigger result[i]] 0 <= i < c.len() ==> result[i] == c[i]),

        pow >= 1 ==> result.len() == 1 + (c.len() - 1) * pow,

        true, // Highest coefficient exists (simplified)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): same implementation */
    if pow == 0 {
        let mut result = vec![0.0; 1];
        result.set(0, 1.0);
        return result;
    }
    
    if pow == 1 {
        return c;
    }
    
    let mut result = c.clone();
    let mut power = 1;
    
    while power < pow
        invariant
            power >= 1,
            power <= pow,
            pow <= maxpower,
            result.len() > 0,
            result.len() == 1 + (c.len() - 1) * power
    {
        result = poly_multiply(result, c);
        power += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}