// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_f64(x: f64) -> f64 { x }
// </vc-helpers>

// <vc-spec>
fn numpy_ceil(x: Vec<f64>) -> (result: Vec<f64>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut res: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            n == x.len(),
        decreases (n - i) as int
    {
        assert(i < n);
        assert(n == x.len());
        assert(i < x.len());
        let xi = x[i];
        let yi = id_f64(xi);
        res.push(yi);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}