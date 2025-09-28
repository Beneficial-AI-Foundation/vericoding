// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn empty_helper(n: u8) -> (v: Vec<f64>)
    ensures
        v.len() == n as usize,
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            v.len() == i,
            i <= n as usize,
        decreases (n as usize) - i,
    {
        v.push(0.0f64);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn empty(n: u8) -> (result: Vec<f64>)
    ensures result.len() == n as usize
// </vc-spec>
// <vc-code>
{
    let result = empty_helper(n);
    result
}
// </vc-code>


}
fn main() {}