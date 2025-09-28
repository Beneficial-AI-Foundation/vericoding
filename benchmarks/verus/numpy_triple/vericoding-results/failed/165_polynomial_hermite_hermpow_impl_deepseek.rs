// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn poly_mul(a: Vec<f64>, b: Vec<f64>, maxpower: usize) -> (result: Vec<f64>)
    requires
        a.len() <= maxpower + 1,
        b.len() <= maxpower + 1,
    ensures
        result.len() <= maxpower + 1,
        (exists|ia: int| 0 <= ia < a.len() && a[ia] != 0.0 && exists|ib: int| 0 <= ib < b.len() && b[ib] != 0.0) ==> 
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
{
    let mut result = Vec::new();
    result.resize(maxpower + 1, 0.0);
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == maxpower + 1,
        decreases a.len() - i,
    {
        let mut j = 0;
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                result.len() == maxpower + 1,
            decreases b.len() - j,
        {
            let idx = i + j;
            if idx <= maxpower {
                result.set(idx, result[idx] + a[i] * b[j]);
            }
            j += 1;
        }
        i += 1;
    }
    
    let mut last_nonzero = 0;
    let mut k = 0;
    while k < result.len()
        invariant
            0 <= k <= result.len(),
            forall|m: int| 0 <= m < k && result[m] != 0.0 ==> m <= last_nonzero,
        decreases result.len() - k,
    {
        if result[k] != 0.0 {
            last_nonzero = k;
        }
        k += 1;
    }
    
    result.truncate(last_nonzero + 1);
    result
}

proof fn pow_zero_prop(c: Vec<f64>, maxpower: usize)
    ensures
        c.len() > 0 ==>
        (let result = hermpow(c, 0, maxpower);
            result.len() == 1 && result[0] == 1.0),
{}

proof fn pow_one_prop(c: Vec<f64>, maxpower: usize)
    ensures
        (c.len() > 0 && c.len() <= maxpower + 1) ==>
        (let result = hermpow(c, 1, maxpower);
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
{}

proof fn non_zero_prop(c: Vec<f64>, pow: usize)
    ensures
        (c.len() > 0 && pow > 0 && exists|i: int| 0 <= i < c.len() && c[i] != 0.0) ==>
        (forall|maxpower: usize| 
            let result = hermpow(c, pow, maxpower);
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0),
{}
// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
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
    /* code modified by LLM (iteration 5): Fixed syntax error - removed let binding */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    }
    
    if pow == 1 {
        return c.clone();
    }
    
    let mut result = c.clone();
    let mut current_pow = 1;
    
    while current_pow < pow
        invariant
            current_pow >= 1,
            current_pow <= pow,
            result.len() <= maxpower + 1,
            result.len() == if c.len() + (c.len() - 1) * (current_pow - 1) <= maxpower + 1 {
                c.len() + (c.len() - 1) * (current_pow - 1)
            } else {
                maxpower + 1
            },
            (exists|i: int| 0 <= i < c.len() && c[i] != 0.0) ==> 
                exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
        decreases pow - current_pow,
    {
        result = poly_mul(result, c.clone(), maxpower);
        current_pow += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}