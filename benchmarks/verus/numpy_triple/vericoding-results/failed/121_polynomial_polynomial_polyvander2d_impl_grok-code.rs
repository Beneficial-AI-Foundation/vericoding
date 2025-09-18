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
/* helper modified by LLM (iteration 4): added spec fn for pow_f64, removed old from invariant to fix compilation */
spec fn pow_f64_spec(base: f64, exp: nat) -> f64
    decreases exp
{
    if exp == 0 {
        1.0
    } else {
        pow_f64_spec(base, (exp - 1) as nat) * base
    }
}
fn pow_f64(base: f64, exp: usize) -> f64
{
    let mut res = 1.0;
    let mut i = 0;
    while i < exp
        invariant
            0 <= i <= exp,
        decreases exp - i,
    {
        res = res * base;
        i = i + 1;
    }
    res
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
/* code modified by LLM (iteration 5): fixed syntax for seq indexing: @y@[k] -> (@y)[k] etc. */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut k = 0;
    while k < x.len()
        invariant
            0 <= k <= x.len(),
            result.len() == k,
            forall|m: int| 0 <= m < k ==> #[trigger] result[m].len() == (x_deg as int + 1) * (y_deg as int + 1),
        decreases x.len() - k,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        while j <= y_deg
            invariant
                0 <= j <= y_deg + 1,
                row.len() == j * (x_deg + 1),
                forall|p: int| 0 <= p < j ==> forall|q: int| 0 <= q <= x_deg ==> #[trigger] row[(p * ((x_deg as int) + 1) + q) as usize] == pow_f64_spec((@y)[k], p as nat) * pow_f64_spec((@x)[k], q as nat),
            decreases y_deg + 1 - j,
        {
            let mut i = 0;
            while i <= x_deg
                invariant
                    0 <= i <= x_deg + 1,
                    row.len() == j * (x_deg + 1) + i,
                    forall|p: int| 0 <= p < j + 1 ==> forall|q: int| 0 <= q < i ==> #[trigger] row[(p * ((x_deg as int) + 1) + q) as usize] == pow_f64_spec((@y)[k], p as nat) * pow_f64_spec((@x)[k], q as nat),
                decreases x_deg + 1 - i,
            {
                row.push(pow_f64(x[k], i) * pow_f64(y[k], j));
                i = i + 1;
            }
            j = j + 1;
        }
        result.push(row);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}