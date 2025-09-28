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
fn pow_f64(base: f64, exp: u8) -> f64
{
    let mut result = 1.0;
    let mut i = 0;
    while i < exp
        invariant
            i <= exp,
        decreases exp - i
    {
        result = result * base;
        i = i + 1;
    }
    result
}

/* helper modified by LLM (iteration 5): added decreases clause to fix loop termination */
// </vc-helpers>

// <vc-spec>
fn polyvander2d(x: Vec<f64>, y: Vec<f64>, x_deg: u8, y_deg: u8) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clauses to all loops */
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == (x_deg as int + 1) * (y_deg as int + 1),
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        
        while j <= x_deg
            invariant
                j <= x_deg + 1,
                row.len() == j as int * (y_deg as int + 1),
            decreases x_deg + 1 - j
        {
            let mut k = 0;
            while k <= y_deg
                invariant
                    k <= y_deg + 1,
                    row.len() == j as int * (y_deg as int + 1) + k as int,
                decreases y_deg + 1 - k
            {
                let x_pow = pow_f64(x[i], j);
                let y_pow = pow_f64(y[i], k);
                row.push(x_pow * y_pow);
                k = k + 1;
            }
            j = j + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}