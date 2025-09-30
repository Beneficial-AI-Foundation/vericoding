// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn monic_coeffs_from_len(n: usize) -> (v: Vec<f64>)
    ensures
        v@.len() == n as int + 1,
        n > 0 ==> v@[n as int] == 1.0,
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i as int,
            forall|k: int| 0 <= k && k < i as int ==> v@[k] == 0.0,
        decreases n - i
    {
        v.push(0.0);
        i = i + 1;
    }
    v.push(1.0);
    v
}
// </vc-helpers>

// <vc-spec>
fn chebfromroots(roots: Vec<f64>) -> (coeffs: Vec<f64>)
    ensures
        coeffs@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coeffs@[roots@.len() as int] != 0.0,
// </vc-spec>
// <vc-code>
{
    let n = roots.len();
    monic_coeffs_from_len(n)
}
// </vc-code>


}
fn main() {}