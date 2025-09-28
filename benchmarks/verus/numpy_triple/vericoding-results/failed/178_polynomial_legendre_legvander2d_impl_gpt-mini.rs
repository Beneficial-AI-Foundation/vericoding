// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pow_f64 with int exponent */
fn pow_f64(base: f64, exp: int) -> f64
    requires
        exp >= 0,
{
    let mut i: int = 0;
    let mut acc: f64 = 1.0;
    while i < exp
        invariant
            0 <= i && i <= exp,
        decreases
            exp - i
    {
        acc = acc * base;
        i = i + 1;
    }
    acc
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
    /* code modified by LLM (iteration 5): implement legvander2d using int indices and pow_f64 */
    let n: int = x.len() as int;
    let degx: int = deg_x as int;
    let degy: int = deg_y as int;
    let mut result: Vec<Vec<f64>> = Vec::new();

    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            (result.len() as int) == i,
        decreases
            n - i
    {
        let xv: f64 = x[i];
        let yv: f64 = y[i];
        let mut row: Vec<f64> = Vec::new();

        let mut ax: int = 0;
        while ax <= degx
            invariant
                0 <= ax && ax <= degx + 1,
                (row.len() as int) == ax * (degy + 1),
            decreases
                (degx + 1) - ax
        {
            let mut by: int = 0;
            while by <= degy
                invariant
                    0 <= by && by <= degy + 1,
                    (row.len() as int) == ax * (degy + 1) + by,
                decreases
                    (degy + 1) - by
            {
                let val: f64 = pow_f64(xv, ax) * pow_f64(yv, by);
                row.push(val);
                by = by + 1;
            }
            ax = ax + 1;
        }

        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}