// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn u8_to_usize(n: u8) -> (m: usize)
    ensures
        m == n as usize,
{
    let m: usize = n as usize;
    m
}
// </vc-helpers>

// <vc-spec>
fn empty(n: u8) -> (result: Vec<f64>)
    ensures result.len() == n as usize
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f64> = Vec::new();
    let target: usize = u8_to_usize(n);
    let mut i: usize = 0usize;
    while i < target
        invariant
            i <= target,
            v.len() == i,
        decreases
            target - i
    {
        v.push(0.0);
        i += 1;
    }
    let result = v;
    result
}
// </vc-code>


}
fn main() {}