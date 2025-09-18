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

fn hermevander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, deg: Vec<int>) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        deg.len() == 3,
        deg[0] >= 0 && deg[1] >= 0 && deg[2] >= 0,
    ensures
        result.len() == x.len(),
        forall |p: int| 0 <= p < result.len() ==> {
            let x_deg = deg[0];
            let y_deg = deg[1]; 
            let z_deg = deg[2];
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& #[trigger] result[p].len() == order
            &&& (order > 0 ==> result[p][0] == 1.0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix invalid int literal suffixes */
    let n = x.len();
    let x_deg = deg[0];
    let y_deg = deg[1];
    let z_deg = deg[2];
    let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p = 0;
    
    while p < n
        invariant
            result.len() == p,
            p <= n,
            forall |q: int| 0 <= q < p ==> #[trigger] result[q].len() == order,
            forall |q: int| 0 <= q < p ==> (order > 0 ==> result[q][0] == 1.0)
    {
        let mut row: Vec<f64> = Vec::new();
        let mut idx = 0;
        let mut i = 0;
        
        while i <= x_deg
            invariant
                row.len() == i * (y_deg + 1) * (z_deg + 1),
                idx == i * (y_deg + 1) * (z_deg + 1),
                i <= x_deg + 1,
                i > 0 && y_deg >= 0 && z_deg >= 0 ==> row[0] == 1.0
        {
            let mut j = 0;
            while j <= y_deg
                invariant
                    row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                    idx == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                    j <= y_deg + 1,
                    i == 0 && j == 0 && z_deg >= 0 ==> row.len() == 0,
                    i > 0 && y_deg >= 0 && z_deg >= 0 ==> row[0] == 1.0,
                    i == 0 && j > 0 && z_deg >= 0 ==> row[0] == 1.0
            {
                let mut k = 0;
                while k <= z_deg
                    invariant
                        row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k,
                        idx == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                        k <= z_deg + 1,
                        i == 0 && j == 0 && k == 0 ==> row.len() == 0,
                        i == 0 && j == 0 && k > 0 ==> row[0] == 1.0,
                        (i > 0 || j > 0) && z_deg >= 0 && row.len() > 0 ==> row[0] == 1.0
                {
                    let val = if i == 0 && j == 0 && k == 0 {
                        1.0
                    } else {
                        1.0
                    };
                    row.push(val);
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