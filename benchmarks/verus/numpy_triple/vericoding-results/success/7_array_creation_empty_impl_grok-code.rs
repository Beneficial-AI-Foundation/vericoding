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
    /* code modified by LLM (iteration 2): Corrected type usage to avoid using nat in exec code */
    let mut v = Vec::new();
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            v.len() == i,
            i <= n as usize,
        decreases (n as usize) - i,
    {
        v.push(0.0);
        i += 1;
    }
    
    v
}
// </vc-code>


}
fn main() {}