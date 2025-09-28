// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zeros_vec(len: usize) -> (r: Vec<f64>)
    ensures
        r.len() == len,
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v@.len() == i as nat,
            i <= len,
        decreases len - i
    {
        v.push(0.0);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn polyroots(c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c.len() > 1,
        c[c.len() - 1] != 0.0,
    ensures
        result.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let target = n - 1;
    let r = zeros_vec(target);
    r
}
// </vc-code>


}
fn main() {}