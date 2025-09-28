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
/* helper modified by LLM (iteration 2): added decreases clauses to all loops to prove termination */
fn pow(base: f64, exp: u8) -> (r: f64)
{
    let mut i: u8 = 0;
    let mut r: f64 = 1.0;
    while i < exp
        invariant
            i <= exp,
        decreases exp - i
    {
        r = r * base;
        i = i + 1;
    }
    r
}

fn compute_row(x_val: f64, y_val: f64, x_deg: u8, y_deg: u8) -> (row: Vec<f64>)
    ensures
        row.len() == (x_deg as nat + 1) * (y_deg as nat + 1),
{
    let mut row = Vec::new();
    let mut j: u8 = 0;
    while j <= y_deg
        invariant
            j as nat <= y_deg as nat + 1,
            row.len() == (x_deg as nat + 1) * (j as nat),
        decreases y_deg - j
    {
        let y_pow = pow(y_val, j);
        let mut i: u8 = 0;
        while i <= x_deg
            invariant
                i as nat <= x_deg as nat + 1,
                j <= y_deg,
                row.len() == (x_deg as nat + 1) * (j as nat) + i as nat,
            decreases x_deg - i
        {
            let x_pow = pow(x_val, i);
            row.push(x_pow * y_pow);
            i = i + 1;
        }
        j = j + 1;
    }
    row
}
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
    /* code modified by LLM (iteration 2): added decreases clause to the loop to prove termination */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut k: usize = 0;
    while k < x.len()
        invariant
            k <= x.len(),
            x.len() == y.len(),
            result.len() == k,
            forall|i: int| 0 <= i < result.len() ==> 
                #[trigger] result[i].len() == (x_deg as int + 1) * (y_deg as int + 1),
        decreases x.len() - k
    {
        let row = compute_row(x[k], y[k], x_deg, y_deg);
        result.push(row);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}