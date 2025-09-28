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
    let mut v = Vec::new();
    let mut i: u8 = 0;
    while i < n
        invariant
            v.len() == i as usize,
            i <= n,
        decreases n - i
    {
        v.push(0.0);
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}