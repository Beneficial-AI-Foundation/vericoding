// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermweight(x: Vec<f32>) -> (w: Vec<f32>)
    requires x.len() > 0,
    ensures
        w.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    let n = x.len();
    let mut w: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            w.len() == i,
        decreases n - i
    {
        w.push(1.0);
        i = i + 1;
    }
    
    w
}
// </vc-code>

}
fn main() {}