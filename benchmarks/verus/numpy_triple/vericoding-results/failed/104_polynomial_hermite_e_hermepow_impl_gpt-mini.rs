// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): polynomial multiplication with proofs */
fn poly_mul(a: Vec<f64>, b: Vec<f64>) -> (result: Vec<f64>)
    requires a.len() > 0 && b.len() > 0,
    ensures result.len() == a.len() + b.len() - 1
{
    let la = a.len();
    let lb = b.len();
    proof { assert(la >= 1 && lb >= 1); }
    let out_len = la + lb - 1;
    let mut result: Vec<f64> = Vec::new();
    let mut k: usize = 0;
    while k < out_len decreases out_len - k {
        result.push(0.0);
        k += 1;
    }
    proof { assert(result.len() == out_len); }
    let mut i: usize = 0;
    while i < la decreases la - i {
        let mut j: usize = 0;
        while j < lb decreases lb - j {
            let idx = i + j;
            proof {
                assert(i < la);
                assert(j < lb);
                assert(la >= 1 && lb >= 1);
                assert(i <= la - 1);
                assert(j <= lb - 1);
                assert(i + j <= (la - 1) + (lb - 1));
                assert(i + j < out_len);
                assert(idx < out_len);
                assert(result.len() == out_len);
            }
            let cur = result[idx];
            result[idx] = cur + a[i] * b[j];
            j += 1;
        }
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): polynomial exponentiation with length proof */
fn poly_pow(c: Vec<f64>, pow: usize) -> (result: Vec<f64>)
    requires c.len() > 0,
    ensures result.len() == 1 + (c.len() - 1) * pow
{
    if pow == 0 {
        let mut result: Vec<f64> = Vec::new();
        result.push(1.0);
        proof { assert(result.len() == 1); }
        result
    } else {
        let mut result = c.clone();
        let mut i: usize = 1;
        while i < pow 
            invariant result.len() == c.len() + (i - 1) * (c.len() - 1)
            decreases pow - i
        {
            result = poly_mul(result, c.clone());
            i += 1;
        }
        proof {
            assert(result.len() == c.len() + (pow - 1) * (c.len() - 1));
            assert(result.len() == 1 + (c.len() - 1) * pow);
        }
        result
    }
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
    /* code modified by LLM (iteration 5): perform hermepow using poly_pow with explicit handling of pow==0 and pow==1 */
    if pow == 0 {
        let mut result: Vec<f64> = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        c
    } else {
        poly_pow(c, pow)
    }
}
// </vc-code>

}
fn main() {}