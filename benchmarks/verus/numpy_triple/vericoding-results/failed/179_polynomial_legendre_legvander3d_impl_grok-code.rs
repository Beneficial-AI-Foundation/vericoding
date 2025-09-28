// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn legendre_all(max_n: usize, x: f32) -> (p: Vec<f32>)
    ensures
        p.len() == max_n + 1,
        p[0] == 1.0f32,
        if max_n >= 1 { p[1] == x } else { true }
{
    let mut p = Vec::with_capacity(max_n + 1);
    p.push(1.0f32);
    if max_n >= 1 {
        p.push(x);
    }
    let mut idx: usize = 2;
    let mut k: f32 = 2.0f32;
    while idx <= max_n
        invariant
            p.len() == idx,
            p[0] == 1.0f32,
            if max_n >= 1 { p[1] == x } else { true },
        decreases (max_n - idx)
    {
        let pkm1 = p[idx - 1];
        let pkm2 = p[idx - 2];
        let n = k;
        let term1 = ((2.0f32 * n - 1.0f32) / n) * x * pkm1;
        let term2 = ((n - 1.0f32) / n) * pkm2;
        p.push(term1 - term2);
        k = k + 1.0f32;
        idx = idx + 1;
    }
    p
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
/* code modified by LLM (iteration 5): added decreases clauses to all loops */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j].len() == (deg_x + 1) * (deg_y + 1) * (deg_z + 1),
            forall |j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
        decreases (x.len() - i)
    {
        let p_x = legendre_all(deg_x, x[i]);
        let p_y = legendre_all(deg_y, y[i]);
        let p_z = legendre_all(deg_z, z[i]);
        let mut row: Vec<f32> = Vec::new();
        let mut ix = 0;
        while ix <= deg_x
            invariant
                row.len() == ix * (deg_y + 1) * (deg_z + 1),
            decreases (deg_x - ix)
        {
            let mut iy = 0;
            while iy <= deg_y
                invariant
                    row.len() == ix * (deg_y + 1) * (deg_z + 1) + iy * (deg_z + 1),
                decreases (deg_y - iy)
            {
                let mut iz = 0;
                while iz <= deg_z
                    invariant
                        row.len() == ix * (deg_y + 1) * (deg_z + 1) + iy * (deg_z + 1) + iz,
                    decreases (deg_z - iz)
                {
                    row.push(p_x[ix] * p_y[iy] * p_z[iz]);
                    iz = iz + 1;
                }
                iy = iy + 1;
            }
            ix = ix + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}