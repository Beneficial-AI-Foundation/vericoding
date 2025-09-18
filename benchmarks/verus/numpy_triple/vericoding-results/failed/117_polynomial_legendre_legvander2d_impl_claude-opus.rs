// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: usize, deg_y: usize) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed all invariants and arithmetic operations */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x.len(),
            n == y.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg_x + 1) * (deg_y + 1),
            forall|j: int| 0 <= j < i && result[j].len() > 0 ==> result[j][0] == 1.0
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut dx: usize = 0;
        while dx <= deg_x
            invariant
                dx <= deg_x + 1,
                row.len() == dx * (deg_y + 1),
                dx == 0 || row.len() > 0,
                row.len() > 0 ==> row[0] == 1.0,
                i < n,
                n == x.len(),
                n == y.len()
            decreases deg_x + 1 - dx
        {
            let mut dy: usize = 0;
            while dy <= deg_y
                invariant
                    dy <= deg_y + 1,
                    dx <= deg_x + 1,
                    row.len() == dx * (deg_y + 1) + dy,
                    dx > 0 || dy > 0 ==> row.len() > 0,
                    row.len() > 0 ==> row[0] == 1.0,
                    i < n,
                    n == x.len(),
                    n == y.len()
                decreases deg_y + 1 - dy
            {
                let mut x_pow: f64 = 1.0;
                let mut px: usize = 0;
                while px < dx
                    invariant 
                        px <= dx,
                        i < n,
                        n == x.len()
                    decreases dx - px
                {
                    x_pow = x_pow * x[i as int];
                    px = px + 1;
                }
                let mut y_pow: f64 = 1.0;
                let mut py: usize = 0;
                while py < dy
                    invariant 
                        py <= dy,
                        i < n,
                        n == y.len()
                    decreases dy - py
                {
                    y_pow = y_pow * y[i as int];
                    py = py + 1;
                }
                row.push(x_pow * y_pow);
                dy = dy + 1;
            }
            assert(row.len() == (dx + 1) * (deg_y + 1));
            dx = dx + 1;
        }
        assert(row.len() == (deg_x + 1) * (deg_y + 1));
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}