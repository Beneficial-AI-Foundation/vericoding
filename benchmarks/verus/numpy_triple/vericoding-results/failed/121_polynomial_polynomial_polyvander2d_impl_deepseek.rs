// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow_spec(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_spec(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed f64 spec operations using proper operators and types */
spec fn compute_term_f64(x: f64, y: f64, i: nat, j: nat) -> f64
    decreases i + j
{
    if i == 0 && j == 0 {
        1.0
    } else if i == 0 {
        y * compute_term_f64(x, y, i, (j - 1) as nat)
    } else {
        x * compute_term_f64(x, y, (i - 1) as nat, j)
    }
}

proof fn compute_term_nonnegative(x: f64, y: f64, i: nat, j: nat)
    requires
        0.0 <= x,
        0.0 <= y
    ensures
        0.0 <= compute_term_f64(x, y, i, j)
    decreases i + j
{
    if i > 0 {
        compute_term_nonnegative(x, y, (i - 1) as nat, j);
    } else if j > 0 {
        compute_term_nonnegative(x, y, i, (j - 1) as nat);
    }
}

spec fn vec_index_f64(v: Vec<f64>, idx: int) -> f64
    requires 0 <= idx < v.len()
{
    v[idx]
}
// </vc-helpers>

// <vc-spec>
fn polyvander2d(x: Vec<f64>, y: Vec<f64>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed f64 operations using proper runtime calculation */
{
    let n = x.len();
    let total_terms = (x_deg + 1) * (y_deg + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|idx: int| 0 <= idx < k ==> #[trigger] result[idx].len() == total_terms,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut i: usize = 0;
        while i <= x_deg
            invariant
                i <= x_deg + 1,
                row.len() == i * (y_deg + 1),
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant
                    j <= y_deg + 1,
                    row.len() == i * (y_deg + 1) + j,
            {
                let x_val = x[k];
                let y_val = y[k];
                let term = x_val.powi(i as i32) * y_val.powi(j as i32);
                row.push(term);
                j += 1;
            }
            i += 1;
        }
        
        assert(row.len() == total_terms) by {
            assert(i == x_deg + 1);
        };
        result.push(row);
        k += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}