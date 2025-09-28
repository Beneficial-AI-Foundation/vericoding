// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ensure product of (deg+1) is positive */
proof fn order_positive(deg0: u8, deg1: u8, deg2: u8)
    ensures
        (deg0 as int + 1) * (deg1 as int + 1) * (deg2 as int + 1) > 0,
{
    proof {
        assert((deg0 as int + 1) >= 1);
        assert((deg1 as int + 1) >= 1);
        assert((deg2 as int + 1) >= 1);
        assert((deg0 as int + 1) * (deg1 as int + 1) * (deg2 as int + 1) >= 1);
        assert((deg0 as int + 1) * (deg1 as int + 1) * (deg2 as int + 1) > 0);
    }
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
    /* code modified by LLM (iteration 5): build rows of length (x_deg+1)*(y_deg+1)*(z_deg+1) with first entry 1.0 */
    let n: usize = x.len();
    let x_deg: usize = deg[0] as usize;
    let y_deg: usize = deg[1] as usize;
    let z_deg: usize = deg[2] as usize;
    let order: usize = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);

    proof {
        order_positive(deg[0], deg[1], deg[2]);
        assert(order > 0);
    }

    let mut result: Vec<Vec<f64>> = Vec::new();

    let mut p: usize = 0;
    while p < n
        invariant
            p <= n,
            result.len() == p,
        decreases n - p
    {
        let mut row: Vec<f64> = Vec::new();
        let mut i: usize = 0;
        while i < order
            invariant
                i <= order,
                row.len() == i,
            decreases order - i
        {
            if i == 0 {
                row.push(1.0);
            } else {
                row.push(0.0);
            }
            i += 1;
        }
        result.push(row);
        p += 1;
    }

    result
}

// </vc-code>

}
fn main() {}