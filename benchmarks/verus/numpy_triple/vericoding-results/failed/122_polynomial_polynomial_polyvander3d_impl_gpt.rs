// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn poly_dim(x_deg: usize, y_deg: usize, z_deg: usize) -> usize {
    (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
}

fn make_vec_zeros(n: usize) -> (v: Vec<f64>)
    ensures
        v.len() == n
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
    {
        v.push(0.0);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|p: int| 0 <= p < result.len() ==> result[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let dims = poly_dim(x_deg, y_deg, z_deg);
    let mut out: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
            forall|p: int| 0 <= p < out@.len() ==> out@[p].len() == dims
    {
        let row = make_vec_zeros(dims);
        out.push(row);
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}