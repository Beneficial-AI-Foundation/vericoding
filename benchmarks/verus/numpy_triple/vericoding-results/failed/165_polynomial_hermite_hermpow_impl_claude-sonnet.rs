// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow and bounds checking */
fn hermite_multiply(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
        a.len() <= usize::MAX / 2,
        b.len() <= usize::MAX / 2,
        a.len() + b.len() > 1,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let mut result = Vec::new();
    let target_len = (a.len() + b.len()) - 1;
    for k in 0..target_len {
        result.push(0.0);
    }
    
    for i in 0..a.len()
        invariant
            result.len() == a.len() + b.len() - 1,
    {
        for j in 0..b.len()
            invariant
                result.len() == a.len() + b.len() - 1,
        {
            let idx = i + j;
            assert(idx < result.len());
            result.set(idx, result[idx] + a[i] * b[j]);
        }
    }
    result
}

fn hermite_power_recursive(c: &Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires
        c.len() > 0,
        pow > 0,
        maxpower < usize::MAX / 2,
    ensures
        result.len() <= maxpower + 1,
        pow == 1 && c.len() <= maxpower + 1 ==> (
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]
        ),
    decreases pow
{
    if pow == 1 {
        if c.len() <= maxpower + 1 {
            c.clone()
        } else {
            let mut truncated = Vec::new();
            for k in 0..(maxpower + 1) {
                truncated.push(0.0);
            }
            for i in 0..(maxpower + 1)
                invariant
                    truncated.len() == maxpower + 1,
                    i <= maxpower + 1,
                    c.len() > maxpower,
            {
                truncated.set(i, c[i]);
            }
            truncated
        }
    } else {
        let prev = hermite_power_recursive(c, pow - 1, maxpower);
        if prev.len() == 0 {
            let mut result = Vec::new();
            result.push(0.0);
            return result;
        }
        let mult_result = hermite_multiply(&prev, c);
        if mult_result.len() <= maxpower + 1 {
            mult_result
        } else {
            let mut truncated = Vec::new();
            for k in 0..(maxpower + 1) {
                truncated.push(0.0);
            }
            for i in 0..(maxpower + 1)
                invariant
                    truncated.len() == maxpower + 1,
                    i <= maxpower + 1,
                    mult_result.len() > maxpower,
            {
                truncated.set(i, mult_result[i]);
            }
            truncated
        }
    }
}
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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow with proper bounds checking */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        if c.len() <= maxpower + 1 {
            c
        } else {
            let mut result = Vec::new();
            for k in 0..(maxpower + 1) {
                result.push(0.0);
            }
            for i in 0..(maxpower + 1)
                invariant
                    result.len() == maxpower + 1,
                    i <= maxpower + 1,
                    c.len() > maxpower,
            {
                result.set(i, c[i]);
            }
            result
        }
    } else {
        if maxpower >= usize::MAX / 2 {
            let mut result = Vec::new();
            result.push(0.0);
            return result;
        }
        hermite_power_recursive(&c, pow, maxpower)
    }
}
// </vc-code>

}
fn main() {}