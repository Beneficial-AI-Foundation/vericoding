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
/* helper modified by LLM (iteration 5): Fixed invariant syntax by removing curly braces */
fn power(base: f64, exp: u8) -> (result: f64)
    ensures result == pow_spec(base as int, exp as nat) as f64
{
    let mut result = 1.0;
    let mut i = 0;
    while i < exp
        invariant
            0 <= i <= exp,
            result == pow_spec(base as int, i as nat) as f64,
        decreases exp - i
    {
        result *= base;
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 5): No changes, code remains the same */
{
    let mut result = Vec::new();
    let n = x.len();
    let x_deg_int = x_deg as int;
    let y_deg_int = y_deg as int;
    let cols = (x_deg_int + 1) * (y_deg_int + 1);
    
    for i in 0..n
        invariant 0 <= i <= n
        invariant result.len() == i
        invariant forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == cols
    {
        let mut row = Vec::with_capacity(cols as usize);
        for a in 0..(x_deg_int + 1)
            invariant 0 <= a <= x_deg_int + 1
            invariant row.len() == a * (y_deg_int + 1)
        {
            let x_power = power(x[i], a as u8);
            for b in 0..(y_deg_int + 1)
                invariant 0 <= b <= y_deg_int + 1
                invariant row.len() == a * (y_deg_int + 1) + b
            {
                let y_power = power(y[i], b as u8);
                row.push(x_power * y_power);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}