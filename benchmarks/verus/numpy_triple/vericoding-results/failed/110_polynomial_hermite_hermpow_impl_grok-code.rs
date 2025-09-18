// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed compilation error by adding exec keyword */
exec fn poly_mul(a: &Vec<f64>, b: &Vec<f64>, max_deg: usize) -> Vec<f64>
    requires max_deg > 0
    decreases max_deg
{
    let mut res: Vec<f64> = Vec::new();
    let mut i = 0;
    while i < max_deg
        invariant i <= max_deg
        decreases max_deg - i
    {
        let mut sum = 0.0f64;
        let mut j = 0;
        while j <= i
            invariant j <= i + 1
            decreases i - j + 1
        {
            if j < a.len() && (i - j) < b.len() {
                sum = sum + a[j] * b[i - j];
            }
            j += 1;
        }
        res.push(sum);
        i += 1;
    }
    res
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
    /* code modified by LLM (iteration 2): implemented hermpow using loop and polys_mul helper */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else {
        let max_len = maxpower + 1;
        let mut current = Vec::new();
        current.push(1.0);
        let mut p = 0;
        while p < pow
            invariant p <= pow
            decreases pow - p
        {
            current = poly_mul(&current, &c, max_len);
            p += 1;
        }
        current
    }
}
// </vc-code>

}
fn main() {}