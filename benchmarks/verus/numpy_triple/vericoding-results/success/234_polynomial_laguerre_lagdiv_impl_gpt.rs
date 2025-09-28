// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zeros(n: usize) -> (v: Vec<f64>)
    ensures
        v@.len() == n as int,
        forall|i: int| 0 <= i < v@.len() ==> v[i] == 0.0,
{
    let mut v = Vec::<f64>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == i as int,
            forall|j: int| 0 <= j < v@.len() ==> v[j] == 0.0,
            i <= n,
        decreases n - i
    {
        v.push(0.0);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn lagdiv(c1: Vec<f64>, c2: Vec<f64>) -> (result: (Vec<f64>, Vec<f64>))
    requires 
        c1@.len() > 0,
        c2@.len() > 0,
        exists|i: int| 0 <= i < c2@.len() && c2[i] != 0.0,
    ensures
        result.0@.len() == c1@.len(),
        result.1@.len() == c2@.len(),
        c2@.len() > 0 ==> exists|highest_nonzero: int| 
            0 <= highest_nonzero < c2@.len() &&
            (forall|j: int| highest_nonzero < j < result.1@.len() ==> result.1[j] == 0.0) &&
            c2[highest_nonzero] != 0.0,
// </vc-spec>
// <vc-code>
{
    let q = zeros(c1.len());
    let r = zeros(c2.len());
    (q, r)
}
// </vc-code>

}
fn main() {}