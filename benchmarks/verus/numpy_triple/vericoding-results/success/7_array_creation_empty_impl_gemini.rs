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
    let mut result: Vec<f64> = Vec::new();
    let n_usize = n as usize;
    while result.len() < n_usize
        invariant
            result.len() <= n_usize,
        decreases n_usize - result.len()
    {
        result.push(0.0f64);
    }
    result
}
// </vc-code>


}
fn main() {}