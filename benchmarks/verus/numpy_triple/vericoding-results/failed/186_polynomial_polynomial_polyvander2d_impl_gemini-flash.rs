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
/* helper modified by LLM (iteration 5): no changes */
spec fn f64_pow_spec(base: f64, exp: nat) -> f64
    decreases exp
{
    if exp == 0 {
        1.0
    } else {
        base * f64_pow_spec(base, (exp - 1) as nat)
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
/* code modified by LLM (iteration 5): corrected invariant for x_power_idx loop and y_power_idx loop to ensure type compatibility. */
{
    let n = x.len();
    let x_basis_size: usize = (x_deg as usize + 1);
    let y_basis_size: usize = (y_deg as usize + 1);
    let total_basis_size: usize = x_basis_size * y_basis_size;

    let mut result = Vec::with_capacity(n);
    let mut i = 0;

    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            result.capacity() == n,
            x.len() == n,
            y.len() == n,
            x_basis_size == (x_deg as usize + 1),
            y_basis_size == (y_deg as usize + 1),
            total_basis_size == x_basis_size * y_basis_size,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == total_basis_size as usize,

        decreases (n - i)
    {
        let mut row = Vec::with_capacity(total_basis_size as usize);
        let mut x_power_idx = 0;

        while x_power_idx <= x_deg
            invariant
                0 <= i as int,
                i < n,
                0 <= x_power_idx,
                x_power_idx <= x_deg + 1,
                row.len() == (x_power_idx as usize * y_basis_size),
                row.capacity() == total_basis_size as usize,
                x.len() == n,
                y.len() == n,
                x_basis_size == (x_deg as usize + 1),
                y_basis_size == (y_deg as usize + 1),
                total_basis_size == x_basis_size * y_basis_size,

            decreases (x_deg + 1 - x_power_idx) as int
        {
            let x_val = x@[i];
            let mut y_power_idx = 0;

            while y_power_idx <= y_deg
                invariant
                    0 <= i as int,
                    i < n,
                    0 <= x_power_idx as int,
                    x_power_idx <= x_deg,
                    0 <= y_power_idx,
                    y_power_idx <= y_deg + 1,
                    row.len() == (x_power_idx as usize * y_basis_size + y_power_idx as usize),
                    row.capacity() == total_basis_size as usize,
                    x.len() == n,
                    y.len() == n,
                    x_basis_size == (x_deg as usize + 1),
                    y_basis_size == (y_deg as usize + 1),
                    total_basis_size == x_basis_size * y_basis_size,

                decreases (y_deg + 1 - y_power_idx) as int
            {
                let y_val = y@[i];

                let term = f64_pow_spec(x_val, x_power_idx as nat) * f64_pow_spec(y_val, y_power_idx as nat);
                row.push(term);
                proof {
                    assert(row.len() == (x_power_idx as usize * y_basis_size + y_power_idx as usize + 1) as usize);
                }
                y_power_idx = y_power_idx + 1;
            }
            x_power_idx = x_power_idx + 1;
        }

        proof {
            assert(row.len() == total_basis_size as usize);
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}