// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): Added decreases clauses to all loops for termination checking */
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == x.len(),
            n == y.len(),
            n == z.len(),
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg_x + 1) * (deg_y + 1) * (deg_z + 1),
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let xi = x[i];
        let yi = y[i];
        let zi = z[i];
        
        let mut dx: usize = 0;
        while dx <= deg_x
            invariant
                dx <= deg_x + 1,
                row.len() == dx * (deg_y + 1) * (deg_z + 1),
                dx > 0 ==> row[0] == 1.0f32,
            decreases deg_x + 1 - dx
        {
            let mut x_pow: f32 = 1.0;
            let mut px: usize = 0;
            while px < dx
                invariant
                    px <= dx,
                decreases dx - px
            {
                x_pow = x_pow * xi;
                px = px + 1;
            }
            
            let mut dy: usize = 0;
            while dy <= deg_y
                invariant
                    dy <= deg_y + 1,
                    row.len() == dx * (deg_y + 1) * (deg_z + 1) + dy * (deg_z + 1),
                    dx > 0 || dy > 0 ==> row[0] == 1.0f32,
                decreases deg_y + 1 - dy
            {
                let mut y_pow: f32 = 1.0;
                let mut py: usize = 0;
                while py < dy
                    invariant
                        py <= dy,
                    decreases dy - py
                {
                    y_pow = y_pow * yi;
                    py = py + 1;
                }
                
                let mut dz: usize = 0;
                while dz <= deg_z
                    invariant
                        dz <= deg_z + 1,
                        row.len() == dx * (deg_y + 1) * (deg_z + 1) + dy * (deg_z + 1) + dz,
                        dx > 0 || dy > 0 || dz > 0 ==> row[0] == 1.0f32,
                    decreases deg_z + 1 - dz
                {
                    let mut z_pow: f32 = 1.0;
                    let mut pz: usize = 0;
                    while pz < dz
                        invariant
                            pz <= dz,
                        decreases dz - pz
                    {
                        z_pow = z_pow * zi;
                        pz = pz + 1;
                    }
                    
                    row.push(x_pow * y_pow * z_pow);
                    dz = dz + 1;
                }
                dy = dy + 1;
            }
            dx = dx + 1;
        }
        
        assert(row.len() == (deg_x + 1) * (deg_y + 1) * (deg_z + 1));
        assert(row[0] == 1.0f32);
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}