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
    let mut i: u8 = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i as usize,
        decreases (n - i) as int
    {
        // We don't care about the content, just the length.
        // The actual value will be overwritten by a subsequent call.
        result.push(0.0);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}