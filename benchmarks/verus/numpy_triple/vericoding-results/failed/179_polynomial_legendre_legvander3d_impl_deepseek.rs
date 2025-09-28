// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type usage and indexing - use f32 instead of int */
fn vander1d(x: &Vec<f32>, deg: usize) -> (v: Vec<f32>)
    ensures
        v.len() == deg + 1,
        v[0] == 1.0f32,
        forall|k: int| 1 <= k < v.len() ==> v[k] == (*x)[k as usize] * v[k - 1],
{
    let mut v = Vec::new();
    v.push(1.0f32);
    let mut k: usize = 1;
    while k <= deg
        invariant
            1 <= v.len() <= deg + 1,
            v[0] == 1.0f32,
            forall|i: int| 1 <= i < v.len() ==> v[i] == (*x)[i as usize] * v[i - 1],
        decreases deg - k,
    {
        let next_val = (*x)[k] * v[k - 1];
        v.push(next_val);
        k = k + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn legvander3d(x: &Vec<f32>, y: &Vec<f32>, z: &Vec<f32>, deg_x: usize, deg_y: usize, deg_z: usize) -> (result: Vec<Vec<f32>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1) * (deg_z + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type conversion issues and ensure proper f32 operations */
{
    let n = x.len();
    let total_coeffs = (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(n);
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == total_coeffs,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
        decreases n - i,
    {
        let mut row = Vec::with_capacity(total_coeffs);
        row.push(1.0f32);
        
        let vx = vander1d(x, deg_x);
        let vy = vander1d(y, deg_y);
        let vz = vander1d(z, deg_z);
        
        let mut kx: usize = 0;
        while kx <= deg_x
            invariant
                row.len() == (kx * (deg_y + 1) * (deg_z + 1)) + 1,
                row[0] == 1.0f32,
            decreases (deg_x + 1) - kx,
        {
            let mut ky: usize = 0;
            while ky <= deg_y
                invariant
                    row.len() == (kx * (deg_y + 1) * (deg_z + 1)) + (ky * (deg_z + 1)) + 1,
                decreases (deg_y + 1) - ky,
            {
                let mut kz: usize = 0;
                while kz <= deg_z
                    invariant
                        row.len() == (kx * (deg_y + 1) * (deg_z + 1)) + (ky * (deg_z + 1)) + kz + 1,
                    decreases (deg_z + 1) - kz,
                {
                    if kx == 0 && ky == 0 && kz == 0 {
                        // Skip the first coefficient (already added as 1.0)
                    } else {
                        let value = vx[kx] * vy[ky] * vz[kz];
                        row.push(value);
                    }
                    kz = kz + 1;
                }
                ky = ky + 1;
            }
            kx = kx + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}