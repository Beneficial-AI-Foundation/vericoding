// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let item = x[i];
        if item != item {
            result.push(0.0);
        } else {
            result.push(item);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}