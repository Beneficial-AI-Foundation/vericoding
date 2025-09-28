// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn empty(n: u8) -> (result: Vec<f64>)
    ensures result.len() == n as usize
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f64> = Vec::new();
    while v.len() < n as usize
        invariant
            v.len() <= n as usize,
        decreases (n as int) - (v.len() as int)
    {
        v.push(0.0);
    }
    v
}
// </vc-code>


}
fn main() {}