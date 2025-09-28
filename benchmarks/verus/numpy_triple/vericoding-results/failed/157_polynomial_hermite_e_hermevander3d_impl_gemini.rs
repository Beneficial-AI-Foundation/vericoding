// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced unsupported integer-to-float cast with a dedicated float counter. */
fn hermval(x: f64, deg: u8) -> (v: Vec<f64>)
    ensures
        v.len() == (deg as nat) + 1,
        v@[0] == 1.0,
{
    let mut v = Vec::new();
    v.push(1.0);
    if deg == 0 {
        return v;
    }
    v.push(x);
    let mut i: usize = 2;
    let mut c: f64 = 1.0;
    while i <= (deg as usize)
        invariant
            deg >= 1,
            2 <= i <= (deg as nat) + 1,
            v.len() == i as nat,
            v@[0] == 1.0,
    {
        let val = x * v[i - 1] - c * v[i - 2];
        v.push(val);
        i = i + 1;
        c = c + 1.0;
    }
    v
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_poly(k: int, t: f64) -> f64
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {

        1.0
    }
}

fn hermevander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, deg: Vec<u8>) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        deg.len() == 3,
        deg[0] as int >= 0 && deg[1] as int >= 0 && deg[2] as int >= 0,
    ensures
        result.len() == x.len(),
        forall |p: int| 0 <= p < result.len() ==> {
            let x_deg = deg[0] as int;
            let y_deg = deg[1] as int; 
            let z_deg = deg[2] as int;
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& #[trigger] result[p].len() == order
            &&& (order > 0 ==> result[p][0] == 1.0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Retained correct nested loop structure from previous attempt. */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p = 0;
    let n_points = x.len();

    let x_deg = deg[0];
    let y_deg = deg[1];
    let z_deg = deg[2];
    let order = (x_deg as usize + 1) * (y_deg as usize + 1) * (z_deg as usize + 1);

    while p < n_points
        invariant
            p <= n_points,
            n_points == x.len(),
            result.len() == p,
            deg.len() == 3,
            deg[0] as int >= 0, deg[1] as int >= 0, deg[2] as int >= 0,
            order == (deg[0] as usize + 1) * (deg[1] as usize + 1) * (deg[2] as usize + 1),
            forall|i: int| 0 <= i < p ==> #[trigger] result[i].len() == order,
            forall|i: int| 0 <= i < p && order > 0 ==> #[trigger] result[i]@[0] == 1.0,
    {
        let xp = x[p];
        let yp = y[p];
        let zp = z[p];

        let vx = hermval(xp, x_deg);
        let vy = hermval(yp, y_deg);
        let vz = hermval(zp, z_deg);

        let mut row: Vec<f64> = Vec::new();
        let mut k: usize = 0;
        while k <= (z_deg as usize)
            invariant
                k <= (z_deg as nat) + 1,
                vx.len() == (x_deg as nat) + 1, vy.len() == (y_deg as nat) + 1, vz.len() == (z_deg as nat) + 1,
                vx@[0] == 1.0, vy@[0] == 1.0, vz@[0] == 1.0,
                row.len() == k * ((y_deg as nat) + 1) * ((x_deg as nat) + 1),
        {
            let mut j: usize = 0;
            while j <= (y_deg as usize)
                invariant
                    k <= (z_deg as nat) + 1, j <= (y_deg as nat) + 1,
                    vx.len() == (x_deg as nat) + 1, vy.len() == (y_deg as nat) + 1, vz.len() == (z_deg as nat) + 1,
                    vx@[0] == 1.0, vy@[0] == 1.0, vz@[0] == 1.0,
                    row.len() == k * ((y_deg as nat) + 1) * ((x_deg as nat) + 1) + j * ((x_deg as nat) + 1),
            {
                let mut i: usize = 0;
                while i <= (x_deg as usize)
                    invariant
                        k <= (z_deg as nat) + 1, j <= (y_deg as nat) + 1, i <= (x_deg as nat) + 1,
                        vx.len() == (x_deg as nat) + 1, vy.len() == (y_deg as nat) + 1, vz.len() == (z_deg as nat) + 1,
                        vx@[0] == 1.0, vy@[0] == 1.0, vz@[0] == 1.0,
                        row.len() == k * ((y_deg as nat) + 1) * ((x_deg as nat) + 1) + j * ((x_deg as nat) + 1) + i,
                {
                    let val = vx[i] * vy[j] * vz[k];
                    row.push(val);
                    i = i + 1;
                }
                j = j + 1;
            }
            k = k + 1;
        }

        assert(row.len() == order);
        assert(order > 0 ==> row@[0] == 1.0);
        
        result.push(row);
        p = p + 1;
    }
    result
}
// </vc-code>

}
fn main() {}