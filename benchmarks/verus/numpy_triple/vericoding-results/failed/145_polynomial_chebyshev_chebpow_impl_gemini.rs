// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [Replaced unsupported vec! macro and assignment to vector elements] */
fn chebmul(a: &Vec<f64>, b: &Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        b.len() > 0,
    ensures
        result.len() == a.len() + b.len() - 1,
{
    let na = a.len();
    let nb = b.len();
    let n = na + nb - 1;

    let mut c = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            c.len() == k,
        decreases n - k
    {
        c.push(0.0f64);
        k = k + 1;
    }

    let mut i: usize = 0;
    while i < na
        invariant
            0 <= i <= na,
            c.len() == n,
        decreases na - i
    {
        let mut j: usize = 0;
        while j < nb
            invariant
                0 <= j <= nb,
                0 <= i < na,
                c.len() == n,
            decreases nb - j
        {
            let val = 0.5f64 * a[i] * b[j];

            let k1 = i + j;
            c.set(k1, c[k1] + val);

            let k2 = if i > j { i - j } else { j - i };
            c.set(k2, c[k2] + val);
            
            j = j + 1;
        }
        i = i + 1;
    }
    c
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
    /* code modified by LLM (iteration 2): [no changes; original logic appears correct] */
    if pow == 0u8 {
        return vec![1.0f64];
    }

    if pow == 1u8 {
        return c;
    }

    // pow >= 2
    let mut result = chebmul(&c, &c);
    let mut i: u8 = 2;

    while i < pow
        invariant
            2 <= i <= pow,
            c.len() > 0,
            result.len() as nat == 1 + (c.len() as nat - 1) * i as nat,
        decreases pow - i
    {
        result = chebmul(&result, &c);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}