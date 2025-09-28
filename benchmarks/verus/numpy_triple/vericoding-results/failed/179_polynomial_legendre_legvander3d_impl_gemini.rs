// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by casting usize to f32 directly */
fn legval(x: f32, deg: usize) -> (v: Vec<f32>)
    ensures
        v.len() == deg + 1,
        v.len() > 0 ==> v[0] == 1.0f32,
{
    let mut v: Vec<f32> = Vec::new();
    if deg == 0 {
        v.push(1.0f32);
        return v;
    }
    
    v.push(1.0f32);
    v.push(x);

    let mut i: usize = 1;
    while i < deg
        invariant
            1 <= i <= deg,
            v.len() == i + 1,
            v[0] == 1.0f32,
        decreases deg - i
    {
        let i_f = i as f32;
        let v_i = v[i];
        let v_i_minus_1 = v[i-1];
        let p_i_plus_1 = ((2.0f32 * i_f + 1.0f32) * x * v_i - i_f * v_i_minus_1) / (i_f + 1.0f32);
        
        v.push(p_i_plus_1);
        i = i + 1;
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
{
    /* code modified by LLM (iteration 5): fixed compilation error in helper, no change to body */
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(n);
    let mut i: usize = 0;

    let total_len = (deg_x + 1) * (deg_y + 1) * (deg_z + 1);

    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == total_len,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j][0] == 1.0f32,
        decreases n - i
    {
        let leg_x = legval(x[i], deg_x);
        let leg_y = legval(y[i], deg_y);
        let leg_z = legval(z[i], deg_z);

        let mut v_row = Vec::with_capacity(total_len);

        let mut dz: usize = 0;
        while dz <= deg_z
            invariant
                0 <= dz <= deg_z + 1,
                v_row.len() == dz * (deg_y + 1) * (deg_x + 1),
            decreases deg_z - dz
        {
            let mut dy: usize = 0;
            while dy <= deg_y
                invariant
                    0 <= dy <= deg_y + 1,
                    v_row.len() == dz * (deg_y + 1) * (deg_x + 1) + dy * (deg_x + 1),
                decreases deg_y - dy
            {
                let mut dx: usize = 0;
                while dx <= deg_x
                    invariant
                        0 <= dx <= deg_x + 1,
                        v_row.len() == dz * (deg_y + 1) * (deg_x + 1) + dy * (deg_x + 1) + dx,
                    decreases deg_x - dx
                {
                    v_row.push(leg_x[dx] * leg_y[dy] * leg_z[dz]);
                    dx = dx + 1;
                }
                dy = dy + 1;
            }
            dz = dz + 1;
        }
        result.push(v_row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}