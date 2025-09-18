// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed from spec to exec fn to allow calls from exec code */
fn min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

fn polymul(p1: &Vec<f64>, p2: &Vec<f64>, max_len: usize) -> (result: Vec<f64>)
    requires
        p1.len() > 0,
        p2.len() > 0,
        max_len > 0,
    ensures
        result.len() == min_usize((p1.len() + p2.len() - 1) as usize, max_len),
{
    let len1 = p1.len();
    let len2 = p2.len();
    let untrun_len = len1 + len2 - 1;
    let res_len = min_usize(untrun_len, max_len);

    let mut result = Vec::new();
    let mut i_init = 0;
    while i_init < res_len
        invariant
            i_init <= res_len,
            result.len() == i_init,
            forall|k: int| 0 <= k < i_init ==> result[k] == 0.0
    {
        result.push(0.0);
        i_init += 1;
    }

    let mut i: usize = 0;
    while i < len1
        invariant 0 <= i <= len1, result.len() == res_len
    {
        let mut j: usize = 0;
        while j < len2
            invariant 0 <= j <= len2, result.len() == res_len
        {
            let k = i + j;
            if k < res_len {
                result.set(k, result[k] + p1[i] * p2[j]);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 5): fixed a compilation error in a helper function */
    if pow == 0 {
        let mut res = Vec::new();
        res.push(1.0);
        return res;
    }

    let max_len = maxpower + 1;
    let c_len = c.len();

    let initial_len = min_usize(c_len, max_len);
    let mut result = Vec::with_capacity(initial_len);
    let mut i: usize = 0;
    while i < initial_len
        invariant
            0 <= i <= initial_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == c[j],
    {
        result.push(c[i]);
        i += 1;
    }
    
    if pow == 1 {
        return result;
    }

    let mut p: usize = 1;
    while p < pow
        invariant
            1 <= p <= pow,
            c.len() == c_len,
            max_len == maxpower + 1,
            c.len() > 0,
            max_len > 0,
            result.len() == min_usize((p * (c_len - 1) + 1) as usize, max_len),
    {
        result = polymul(&result, &c, max_len);
        p = p + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}