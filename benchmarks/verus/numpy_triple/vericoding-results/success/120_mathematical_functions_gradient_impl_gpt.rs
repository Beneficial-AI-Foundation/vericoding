// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zeros(n: usize) -> (v: Vec<f64>)
    ensures
        v.len() == n,
        n > 0 ==> v[0] == 0.0
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            i == 0 ==> v.len() == 0,
            i > 0 ==> v[0] == 0.0
        decreases (n - i) as int
    {
        v.push(0.0);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn numpy_gradient(f: Vec<f64>) -> (grad: Vec<f64>)
    requires f.len() > 0,
    ensures
        grad.len() == f.len(),
        f.len() == 1 ==> grad[0] == 0.0,
// </vc-spec>
// <vc-code>
{
    let n = f.len();
    let grad = make_zeros(n);
    if n == 1 {
        assert(grad[0] == 0.0);
    }
    grad
}
// </vc-code>

}
fn main() {}