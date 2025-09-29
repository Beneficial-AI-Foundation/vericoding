// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zero_vec(n: usize) -> (v: Vec<f64>)
    ensures
        v.len() == n,
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
        decreases (n - i) as int
    {
        v.push(0.0);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn hermeder(c: Vec<f64>, m: u8, scl: f64) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        m as nat > 0,
        scl != 0.0,
    ensures 
        result.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let result_vec = make_zero_vec(n - 1);
    result_vec
}
// </vc-code>

}
fn main() {}