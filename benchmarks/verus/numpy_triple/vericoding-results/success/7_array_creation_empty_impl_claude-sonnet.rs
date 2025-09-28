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
    /* code modified by LLM (iteration 2): added decreases clause */
    let mut result = Vec::new();
    let mut i: u8 = 0;
    while i < n
        invariant
            result.len() == i as usize,
            i <= n,
        decreases n - i
    {
        result.push(0.0);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}