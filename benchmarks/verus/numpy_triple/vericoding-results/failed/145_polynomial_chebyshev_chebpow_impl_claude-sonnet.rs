// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat type usage by using ghost variables and regular usize arithmetic */
fn cheb_multiply(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
        a.len() <= usize::MAX,
        b.len() <= usize::MAX,
        a.len() + b.len() > 1,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    ghost let a_len = a.len() as nat;
    ghost let b_len = b.len() as nat;
    let result_len = a.len() + b.len() - 1;
    let mut result = Vec::new();
    
    let mut idx = 0;
    while idx < result_len
        invariant
            result.len() == idx,
            idx <= result_len,
        decreases result_len - idx
    {
        result.push(0.0);
        idx += 1;
    }
    
    for i in 0..a.len()
        invariant
            result.len() == a.len() + b.len() - 1,
    {
        for j in 0..b.len()
            invariant
                result.len() == a.len() + b.len() - 1,
        {
            let sum_idx = i + j;
            if sum_idx < result.len() {
                let old_val = result[sum_idx];
                result.set(sum_idx, old_val + a[i] * b[j]);
            }
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn chebpow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        pow <= maxpower,
    ensures
        /* Special case: pow = 0 returns [1.0] */
        (pow as nat == 0) ==> (result.len() == 1 && result[0] == 1.0),
        /* Special case: pow = 1 returns input unchanged */
        (pow as nat == 1) ==> (result.len() == c.len() && 
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        /* Result length is correct */
        result.len() == (if pow as nat == 0 { 1 } else { 1 + (c.len() - 1) * pow as nat }),
        /* For pow > 1: first coefficient exists when appropriate */
        (pow as nat > 1 && c.len() >= 1) ==> (result.len() > 0),
        /* Non-triviality for pow >= 2 with sufficient input length */
        (pow as nat >= 2 && c.len() >= 2 && result.len() > 2) ==> 
            (result[0] != 0.0 || result[1] != 0.0 || result[2] != 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat type usage in executable code */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    }
    
    if pow == 1 {
        return c;
    }
    
    let mut result = c.clone();
    let mut p = 1;
    
    while p < pow
        invariant
            p >= 1,
            p <= pow,
            result.len() > 0,
            result.len() == 1 + (c.len() - 1) * p as nat,
        decreases pow - p
    {
        proof {
            assert(result.len() > 0);
            assert(c.len() > 0);
            assert(result.len() + c.len() > 1);
        }
        result = cheb_multiply(&result, &c);
        p += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}