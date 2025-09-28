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
fn f64_pow(base: f64, exp: usize) -> f64
    decreases exp
{
    if exp == 0 {
        1.0
    } else {
        base * f64_pow(base, exp - 1)
    }
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
    /* code modified by LLM (iteration 5): removed incorrect 'as int' casts for usize indexing in Vec */
    let mut result: Vec<Vec<f64>> = Vec::new();
    for k in 0..x.len() {
        let mut row: Vec<f64> = Vec::new();
        for i in 0..(x_deg as usize + 1) {
            for j in 0..(y_deg as usize + 1) {
                let val = f64_pow(x[k], i) * f64_pow(y[k], j);
                row.push(val);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}