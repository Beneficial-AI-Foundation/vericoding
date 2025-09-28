// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow and bounds checking */
fn poly_convolution(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
        result.len() > 0,
{
    let mut result = Vec::new();
    let mut i = 0;
    let result_len = (a.len() + b.len()) - 1;
    
    while i < result_len
        invariant
            i <= result_len,
            result.len() == i,
            a.len() > 0,
            b.len() > 0,
            result_len == a.len() + b.len() - 1,
        decreases result_len - i
    {
        let mut sum = 0.0;
        let mut j = 0;
        
        while j <= i && j < b.len()
            invariant
                j <= i + 1,
                j <= b.len(),
                i < result_len,
                result_len == a.len() + b.len() - 1,
                a.len() > 0,
                i >= j ==> i - j < a.len(),
            decreases b.len() - j
        {
            if i >= j && i - j < a.len() {
                sum += b[j] * a[i - j];
            }
            j += 1;
        }
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): strengthened invariant to handle result size correctly */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        c
    } else {
        let mut result = c.clone();
        let mut current_pow = 1;
        
        while current_pow < pow
            invariant
                current_pow >= 1,
                current_pow <= pow,
                result.len() > 0,
                current_pow == 1 ==> result.len() == c.len(),
                current_pow > 1 ==> result.len() == 1 + (c.len() - 1) * current_pow as int,
                result.len() > 0,
            decreases pow - current_pow
        {
            result = poly_convolution(&result, &c);
            current_pow += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}