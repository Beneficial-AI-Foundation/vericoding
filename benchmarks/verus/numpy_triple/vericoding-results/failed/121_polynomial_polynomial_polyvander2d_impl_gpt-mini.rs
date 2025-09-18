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
/* helper modified by LLM (iteration 5): compute row length for each result row */
spec fn poly_row_len(x_deg: usize, y_deg: usize) -> usize { (x_deg + 1) * (y_deg + 1) }
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
{
    /* code modified by LLM (iteration 5): build Vandermonde 2D matrix filling powers */
    let m: usize = x.len();
    let row_len: usize = poly_row_len(x_deg, y_deg);

    let mut result: Vec<Vec<f64>> = Vec::new();

    let mut i: usize = 0;
    while i < m
        invariant i <= m && result.len() == i
        decreases m - i
    {
        let xi: f64 = x[i];
        let yi: f64 = y[i];

        let mut row: Vec<f64> = Vec::new();

        let mut yy: usize = 0;
        while yy <= y_deg
            invariant yy <= y_deg + 1 && row.len() == yy * (x_deg + 1)
            decreases (y_deg + 1) - yy
        {
            let mut xx: usize = 0;
            while xx <= x_deg
                invariant xx <= x_deg + 1 && row.len() == yy * (x_deg + 1) + xx
                decreases (x_deg + 1) - xx
            {
                let val: f64 = xi.powi(xx as i32) * yi.powi(yy as i32);
                row.push(val);
                xx += 1;
            }

            yy += 1;
        }

        result.push(row);
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}