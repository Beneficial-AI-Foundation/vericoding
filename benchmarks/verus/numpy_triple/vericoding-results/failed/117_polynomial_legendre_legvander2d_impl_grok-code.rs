// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax in legendre polynomials generation function for better compilation; adjusted invariants and decreases */
fn legendre_polys(x: f64, deg: usize) -> (polys: Vec<f64>) {
    if deg == 0 {
        vec![1.0f64]
    } else {
        let mut polys = vec![1.0f64, x];
        let mut n: int = 1;
        while n < deg as int
        invariant n <= deg as int
        decreases deg as int - n
        {
            let next = ((2 * n + 1) as f64 * x * polys[n] - n as f64 * polys[n - 1]) / ((n + 1) as f64);
            polys.push(next);
            n += 1;
        }
        polys
    }
}
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
/* code modified by LLM (iteration 5): Fixed compilation syntax errors in loop invariants by adjusting indentation; implemented legvander2d logic with proper indexing for Vecs */
let mut result: Vec<Vec<f64>> = Vec::new();
let mut i: int = 0;
while i < x.len() as int
    invariant i <= x.len() as int
    invariant result.len() == i
    invariant forall|j: int| 0 <= j < i ==> result@[j].len() == (deg_x as int + 1) * (deg_y as int + 1)
    decreases x.len() as int - i
{
    let x_polys = legendre_polys(x@[i], deg_x);
    let y_polys = legendre_polys(y@[i], deg_y);
    let mut row: Vec<f64> = Vec::new();
    let mut kx: int = 0;
    while kx < x_polys.len() as int
        invariant kx <= x_polys.len() as int
        invariant row.len() == kx * (y_polys.len() as int)
        decreases x_polys.len() as int - kx
    {
        let mut ky: int = 0;
        while ky < y_polys.len() as int
            invariant ky <= y_polys.len() as int
            invariant row.len() == kx * (y_polys.len() as int) + ky
            decreases y_polys.len() as int - ky
        {
            row.push(x_polys@[kx] * y_polys@[ky]);
            ky += 1;
        }
        kx += 1;
    }
    result.push(row);
    i += 1;
}
result
}
// </vc-code>

}
fn main() {}