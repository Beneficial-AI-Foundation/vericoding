// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed f64 conversion to use executable cast] */
fn legval(v: f64, deg: u8) -> (c: Vec<f64>)
    ensures
        c.len() == deg as int + 1,
        c.len() > 0 ==> c[0] == 1.0,
        deg >= 1 ==> c[1] == v,
{
    let mut c = Vec::new();
    c.push(1.0);

    if deg >= 1 {
        c.push(v);
    }

    let mut d: u8 = 1;
    while d < deg
        invariant
            d <= deg,
            c.len() == d as int + 1,
            c.len() > 0 ==> c[0] == 1.0,
            d >= 1 ==> c[1] == v,
        decreases deg - d
    {
        let d_f = d as f64;
        let val = ((2.0 * d_f + 1.0) * v * c[d as usize] - d_f * c[d as usize - 1]) / (d_f + 1.0);
        c.push(val);
        d = d + 1;
    }

    c
}
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
    /* code modified by LLM (iteration 5): [re-submitted plausible implementation to see new errors after fixing helper] */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            x.len() == y.len(),
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg_x as int + 1) * (deg_y as int + 1),
            forall|j: int| 0 <= j < i && result[j].len() > 0 ==> result[j][0] == 1.0,
        decreases x.len() - i
    {
        let v_x = legval(x[i], deg_x);
        let v_y = legval(y[i], deg_y);

        let mut row = Vec::new();
        let mut j: usize = 0;
        while j <= (deg_x as usize)
            invariant
                0 <= j <= (deg_x as usize) + 1,
                v_x.len() == deg_x as int + 1,
                v_y.len() == deg_y as int + 1,
                row.len() == j * (deg_y as usize + 1),
            decreases (deg_x as usize) + 1 - j
        {
            let mut k: usize = 0;
            while k <= (deg_y as usize)
                invariant
                    0 <= k <= (deg_y as usize) + 1,
                    j <= (deg_x as usize),
                    row.len() == j * (deg_y as usize + 1) + k,
                decreases (deg_y as usize) + 1 - k
            {
                row.push(v_x[j] * v_y[k]);
                k = k + 1;
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}