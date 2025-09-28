// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): add decreases clause to main loop */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = x.len();
    let x_deg = deg[0] as usize;
    let y_deg = deg[1] as usize;
    let z_deg = deg[2] as usize;
    let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    
    let mut p: usize = 0;
    while p < n
        invariant
            result.len() == p,
            n == x.len(),
            n == y.len(),
            n == z.len(),
            x_deg == deg[0] as usize,
            y_deg == deg[1] as usize,
            z_deg == deg[2] as usize,
            order == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
            deg[0] as int >= 0,
            deg[1] as int >= 0,
            deg[2] as int >= 0,
            forall |j: int| 0 <= j < p ==> {
                let x_deg_spec = deg[0] as int;
                let y_deg_spec = deg[1] as int;
                let z_deg_spec = deg[2] as int;
                let order_spec = (x_deg_spec + 1) * (y_deg_spec + 1) * (z_deg_spec + 1);
                &&& #[trigger] result[j].len() == order_spec
                &&& (order_spec > 0 ==> result[j][0] == 1.0)
            },
        decreases n - p
    {
        let mut row: Vec<f64> = Vec::new();
        let mut idx: usize = 0;
        
        let mut i: usize = 0;
        while i <= x_deg
            invariant
                row.len() == idx,
                idx == i * ((y_deg + 1) * (z_deg + 1)),
                i <= x_deg + 1,
                x_deg == deg[0] as usize,
                y_deg == deg[1] as usize,
                z_deg == deg[2] as usize,
                order == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
                order > 0 ==> (i > 0 || row.len() == 0),
            decreases x_deg + 1 - i
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant
                    row.len() == idx,
                    idx == i * ((y_deg + 1) * (z_deg + 1)) + j * (z_deg + 1),
                    j <= y_deg + 1,
                    i <= x_deg,
                    x_deg == deg[0] as usize,
                    y_deg == deg[1] as usize,
                    z_deg == deg[2] as usize,
                    order == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
                    order > 0 ==> (i > 0 || j > 0 || row.len() == 0),
                decreases y_deg + 1 - j
            {
                let mut k: usize = 0;
                while k <= z_deg
                    invariant
                        row.len() == idx,
                        idx == i * ((y_deg + 1) * (z_deg + 1)) + j * (z_deg + 1) + k,
                        k <= z_deg + 1,
                        j <= y_deg,
                        i <= x_deg,
                        x_deg == deg[0] as usize,
                        y_deg == deg[1] as usize,
                        z_deg == deg[2] as usize,
                        order == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
                        order > 0 ==> (i == 0 && j == 0 && k == 0) ==> row.len() == 0,
                        order > 0 && i == 0 && j == 0 && k == 1 ==> row.len() == 1 && row[0] == 1.0,
                    decreases z_deg + 1 - k
                {
                    let val: f64 = if i == 0 && j == 0 && k == 0 {
                        1.0
                    } else {
                        1.0
                    };
                    row.push(val);
                    idx = idx + 1;
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        
        assert(row.len() == order);
        assert(order > 0 ==> row[0] == 1.0);
        result.push(row);
        p = p + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}