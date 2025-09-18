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
/* code modified by LLM (iteration 5): Fixed the issue where `row.len()` invariant for the inner `while dy` loop was incorrectly specified by adding `dx * (y_deg + 1)` which effectively represents the accumulation of `y` terms. */
{
    let n = x.len();
    let num_cols = (x_deg + 1) * (y_deg + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();

    let mut i = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == num_cols
    {
        let mut row: Vec<f64> = Vec::new();
        let current_x = x.get(i).unwrap();
        let current_y = y.get(i).unwrap();

        let mut dx = 0;
        while dx <= x_deg
            invariant
                0 <= dx as int <= x_deg as int + 1,
                row.len() == dx * (y_deg + 1),
                result.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == num_cols
        {
            let x_term = current_x.powf(dx as f64);
            let mut dy = 0;
            while dy <= y_deg
                invariant
                    0 <= dy as int <= y_deg as int + 1,
                    row.len() == (dx * (y_deg + 1)) + dy,
                    result.len() == i,
                    forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == num_cols
            {
                let y_term = current_y.powf(dy as f64);
                row.push((x_term * y_term));
                dy = dy + 1;
            }
            dx = dx + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}