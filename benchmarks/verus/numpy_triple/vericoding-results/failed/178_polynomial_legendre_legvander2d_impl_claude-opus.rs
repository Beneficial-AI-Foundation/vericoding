// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: u8, deg_y: u8) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x as int + 1) * (deg_y as int + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to all while loops */
    let n = x.len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg_x as int + 1) * (deg_y as int + 1),
            forall|j: int| 0 <= j < i && result[j].len() > 0 ==> result[j][0] == 1.0,
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut dx: u8 = 0;
        while dx <= deg_x
            invariant
                dx <= deg_x + 1,
                row.len() == dx as int * (deg_y as int + 1),
                dx > 0 ==> row[0] == 1.0,
            decreases (deg_x as int + 1) - (dx as int)
        {
            let mut dy: u8 = 0;
            while dy <= deg_y
                invariant
                    dy <= deg_y + 1,
                    row.len() == dx as int * (deg_y as int + 1) + dy as int,
                    dx == 0 && dy == 0 || row.len() == 0 || row[0] == 1.0,
                decreases (deg_y as int + 1) - (dy as int)
            {
                let mut x_power: f64 = 1.0;
                let mut px: u8 = 0;
                while px < dx
                    invariant
                        px <= dx,
                    decreases (dx as int) - (px as int)
                {
                    x_power = x_power * x[i];
                    px = px + 1;
                }
                let mut y_power: f64 = 1.0;
                let mut py: u8 = 0;
                while py < dy
                    invariant
                        py <= dy,
                    decreases (dy as int) - (py as int)
                {
                    y_power = y_power * y[i];
                    py = py + 1;
                }
                row.push(x_power * y_power);
                dy = dy + 1;
            }
            dx = dx + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}