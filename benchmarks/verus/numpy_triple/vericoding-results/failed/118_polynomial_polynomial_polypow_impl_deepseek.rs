// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn polynomial_multiplication(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len() - 1,
        forall|k: int| 0 <= k < result.len() as int ==>
            result@[k] == sum(0, a.len() as int, |i: int| if 0 <= i < a.len() as int && 0 <= k - i < b.len() as int { a[i as usize] as f32 * b[(k - i) as usize] as f32 } else { 0.0f32 })
{
    let mut result = Vec::<f32>::new();
    let total_len = (a.len() + b.len() - 1) as usize;
    result.resize(total_len, 0.0f32);
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == total_len,
            forall|k: int| 0 <= k < result.len() as int ==>
                result@[k] == sum(0, i as int, |j: int| if 0 <= j < i as int && 0 <= k - j < b.len() as int { a[j as usize] as f32 * b[(k - j) as usize] as f32 } else { 0.0f32 }),
    {
        let mut k: usize = 0;
        while k < b.len()
            invariant
                0 <= k <= b.len(),
                result.len() == total_len,
                forall|idx: int| 0 <= idx < result.len() as int ==> 
                    result@[idx] == sum(0, i as int, |j: int| if 0 <= j < i as int && 0 <= idx - j < b.len() as int { a[j as usize] as f32 * b[(idx - j) as usize] as f32 } else { 0.0f32 })
                    + sum(0, k as int, |temp: int| if i as int <= idx && idx == i as int + temp as int && temp < k as int && temp < b.len() as int { a[i] as f32 * b[temp as usize] as f32 } else { 0.0f32 }),
        {
            let idx = i + k;
            let current_val = result[idx];
            let new_val = current_val + (a[i] as f32 * b[k] as f32);
            result.set(idx as usize, new_val);
            k = k + 1;
        }
        i = i + 1;
    }
    result
}

spec fn sum(start: int, end: int, f: spec_fn(int) -> f32) -> f32 {
    if start >= end {
        0.0f32
    } else {
        f(start) + sum(start + 1, end, f)
    }
}

proof fn lemma_poly_mult_base_one()
    ensures
        sum(0, 1, |i: int| if i >= 0 { 1.0f32 } else { 0.0f32 }) == 1.0f32
{
}

proof fn lemma_poly_mult_base_zero()
    ensures
        sum(0, 0, |_: int| 0.0f32) == 0.0f32
{
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting and arithmetic operations */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0f32);
        result
    } else if pow == 1 {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                result.len() == i,
                forall|k: int| 0 <= k < i as int ==> result[k as usize] == c[k as usize],
        {
            result.push(c[i]);
            i = i + 1;
        }
        result
    } else {
        let half_pow = pow / 2;
        let half_result = polypow(c, half_pow);
        let square_result = polynomial_multiplication(half_result, half_result);
        
        if pow % 2 == 0 {
            square_result
        } else {
            polynomial_multiplication(square_result, c)
        }
    }
}
// </vc-code>

}
fn main() {}