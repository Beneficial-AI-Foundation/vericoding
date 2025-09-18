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
/* code modified by LLM (iteration 5): restructured inner loops to avoid overflow and fixed indexing */
{
    let n = x.len();
    let mut result = Vec::with_capacity(n);
    for i in 0..n
        invariant 0 <= i <= n,
                i < x.len(),
                i < y.len(),
                result.len() == i
    {
        let mut row = Vec::new();
        
        // Compute x powers: [1, x[i], x[i]^2, ..., x[i]^x_deg]
        let mut x_powers = Vec::new();
        x_powers.push(1.0);   // x^0
        for a in 0..x_deg
            invariant 0 <= a <= x_deg,
                    x_powers.len() == a + 1
        {
            let next_power = x_powers[a] * x[i];
            x_powers.push(next_power);
        }

        // Compute y powers: [1, y[i], y[i]^2, ..., y[i]^y_deg]
        let mut y_powers = Vec::new();
        y_powers.push(1.0);   // y^0
        for b in 0..y_deg
            invariant 0 <= b <= y_deg,
                    y_powers.len() == b + 1
        {
            let next_power = y_powers[b] * y[i];
            y_powers.push(next_power);
        }

        // Generate all monomials: x^a * y^b for a in [0, x_deg] and b in [0, y_deg]
        for a in 0..x_powers.len() {
            for b in 0..y_powers.len() {
                let monomial = x_powers[a] * y_powers[b];
                row.push(monomial);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}