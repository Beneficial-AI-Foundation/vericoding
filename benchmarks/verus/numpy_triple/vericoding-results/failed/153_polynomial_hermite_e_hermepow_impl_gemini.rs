// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn poly_mul(p1: &Vec<f64>, p2: &Vec<f64>) -> (result: Vec<f64>)
    requires
        p1.len() > 0,
        p2.len() > 0,
    ensures
        result.len() == p1.len() + p2.len() - 1,
{
    let len1 = p1.len();
    let len2 = p2.len();
    let res_len = len1 + len2 - 1;

    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < res_len
        invariant
            0 <= k <= res_len,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result@[i] == 0.0,
        decreases res_len - k
    {
        result.push(0.0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < len1
        invariant
            0 <= i <= len1,
            result.len() == res_len,
        decreases len1 - i
    {
        let mut j: usize = 0;
        while j < len2
            invariant
                0 <= j <= len2,
                i < len1,
                result.len() == res_len,
            decreases len2 - j
        {
            let k = i + j;
            let val = result[k] + p1[i] * p2[j];
            result.set(k, val);
            j += 1;
        }
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
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    }

    let mut result = c.clone();
    let mut current_pow: u8 = 1;

    while current_pow < pow
        invariant
            1 <= current_pow,
            current_pow <= pow,
            c.len() > 0,
            result.len() == 1 + (c.len() - 1) * (current_pow as int),
        decreases pow - current_pow
    {
        result = poly_mul(&result, &c);
        current_pow = current_pow + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}