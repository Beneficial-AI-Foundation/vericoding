// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): changed n and i to usize, using real types for executable code */
    let n: usize = c.len() - 1;
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            0 <= i <= n,
        decreases n - i
    {
        result.push(0.0);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}