// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|p: int| 0 <= p < result.len() ==> result[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariant and overflow issues */
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|p: int| 0 <= p < i ==> result[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
        decreases n - i,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut idx_z: usize = 0;
        while idx_z <= z_deg
            invariant
                idx_z <= z_deg + 1,
                row.len() == idx_z * (y_deg + 1) * (x_deg + 1),
                i < n,
            decreases z_deg + 1 - idx_z,
        {
            let mut idx_y: usize = 0;
            while idx_y <= y_deg
                invariant
                    idx_y <= y_deg + 1,
                    idx_z <= z_deg,
                    row.len() == idx_z * (y_deg + 1) * (x_deg + 1) + idx_y * (x_deg + 1),
                    i < n,
                decreases y_deg + 1 - idx_y,
            {
                let mut idx_x: usize = 0;
                while idx_x <= x_deg
                    invariant
                        idx_x <= x_deg + 1,
                        idx_y <= y_deg,
                        idx_z <= z_deg,
                        row.len() == idx_z * (y_deg + 1) * (x_deg + 1) + idx_y * (x_deg + 1) + idx_x,
                        i < n,
                    decreases x_deg + 1 - idx_x,
                {
                    let mut x_pow: f64 = 1.0;
                    let mut x_count: usize = 0;
                    while x_count < idx_x
                        invariant
                            x_count <= idx_x,
                            i < n,
                        decreases idx_x - x_count,
                    {
                        x_pow = x_pow * x[i];
                        x_count = x_count + 1;
                    }
                    let mut y_pow: f64 = 1.0;
                    let mut y_count: usize = 0;
                    while y_count < idx_y
                        invariant
                            y_count <= idx_y,
                            i < n,
                        decreases idx_y - y_count,
                    {
                        y_pow = y_pow * y[i];
                        y_count = y_count + 1;
                    }
                    let mut z_pow: f64 = 1.0;
                    let mut z_count: usize = 0;
                    while z_count < idx_z
                        invariant
                            z_count <= idx_z,
                            i < n,
                        decreases idx_z - z_count,
                    {
                        z_pow = z_pow * z[i];
                        z_count = z_count + 1;
                    }
                    row.push(x_pow * y_pow * z_pow);
                    idx_x = idx_x + 1;
                }
                idx_y = (idx_y + 1) as usize;
            }
            idx_z = (idx_z + 1) as usize;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}