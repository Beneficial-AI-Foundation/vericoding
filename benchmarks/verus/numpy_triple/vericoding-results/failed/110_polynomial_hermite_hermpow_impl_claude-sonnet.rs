// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed polynomial_mult_len to spec function */
spec fn polynomial_mult_len(a_len: usize, b_len: usize) -> usize
{
    if a_len == 0 || b_len == 0 { 0 } else { a_len + b_len - 1 }
}

fn polynomial_mult(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires a.len() > 0, b.len() > 0
    ensures result.len() == polynomial_mult_len(a.len(), b.len())
{
    let target_len = if a.len() == 0 || b.len() == 0 { 0 } else { a.len() + b.len() - 1 };
    let mut result = Vec::with_capacity(target_len);
    for k in 0..target_len
        invariant result.len() == k
    {
        result.push(0.0);
    }
    for i in 0..a.len()
        invariant result.len() == target_len
    {
        for j in 0..b.len()
            invariant result.len() == target_len
        {
            result.set(i + j, result[i + j] + a[i] * b[j]);
        }
    }
    result
}

fn polynomial_power(c: Vec<f64>, pow: usize) -> (result: Vec<f64>)
    requires c.len() > 0
    ensures result.len() > 0
    decreases pow
{
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        c
    } else {
        let half_pow = polynomial_power(c.clone(), pow / 2);
        if pow % 2 == 0 {
            polynomial_mult(half_pow.clone(), half_pow)
        } else {
            polynomial_mult(c, polynomial_mult(half_pow.clone(), half_pow))
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        maxpower >= 0,
    ensures

        result.len() <= maxpower + 1,
        result.len() == if c.len() + (c.len() - 1) * pow <= maxpower + 1 {
            c.len() + (c.len() - 1) * pow
        } else {
            maxpower + 1
        },

        pow == 0 ==> result.len() == 1 && result[0] == 1.0,

        (pow == 1 && c.len() <= maxpower + 1) ==> (
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]
        ),

        ((exists|i: int| 0 <= i < c.len() && c[i] != 0.0) && pow > 0) ==> 
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, compilation error was in helpers */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else {
        let full_result = polynomial_power(c, pow);
        if full_result.len() <= maxpower + 1 {
            full_result
        } else {
            let mut truncated = Vec::new();
            for i in 0..(maxpower + 1)
                invariant truncated.len() == i
            {
                truncated.push(full_result[i]);
            }
            truncated
        }
    }
}
// </vc-code>

}
fn main() {}