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
    /* code modified by LLM (iteration 5): fix arithmetic overflow and invariant issues */
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == k,
            k <= n,
            n == x.len(),
            n == y.len(),
            forall|idx: int| 0 <= idx < k ==> #[trigger] result[idx].len() == (x_deg + 1) * (y_deg + 1),
        decreases n - k
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j <= y_deg
            invariant
                row.len() == j * (x_deg + 1),
                j <= y_deg + 1,
                k < n,
                n == x.len(),
                n == y.len(),
            decreases (y_deg + 1) - j
        {
            let mut i: usize = 0;
            while i <= x_deg
                invariant
                    row.len() == j * (x_deg + 1) + i,
                    i <= x_deg + 1,
                    j <= y_deg,
                    k < n,
                    n == x.len(),
                    n == y.len(),
                decreases (x_deg + 1) - i
            {
                let x_val: f64 = x[k];
                let y_val: f64 = y[k];
                let mut x_power: f64 = 1.0;
                let mut exp_i: usize = 0;
                while exp_i < i
                    invariant exp_i <= i
                    decreases i - exp_i
                {
                    x_power = x_power * x_val;
                    exp_i = exp_i + 1;
                }
                let mut y_power: f64 = 1.0;
                let mut exp_j: usize = 0;
                while exp_j < j
                    invariant exp_j <= j
                    decreases j - exp_j
                {
                    y_power = y_power * y_val;
                    exp_j = exp_j + 1;
                }
                let product: f64 = x_power * y_power;
                row.push(product);
                assert(i < x_deg + 1);
                i = (i + 1) as usize;
            }
            assert(j < y_deg + 1);
            j = (j + 1) as usize;
        }
        assert(row.len() == (x_deg + 1) * (y_deg + 1));
        result.push(row);
        k = (k + 1) as usize;
    }
    result
}
// </vc-code>

}
fn main() {}