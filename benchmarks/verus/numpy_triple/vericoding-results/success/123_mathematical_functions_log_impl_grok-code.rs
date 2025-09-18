// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn log(x: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i as int] > 0,
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added decreases clause to the while loop for termination */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            0 <= i <= x.len()
        decreases x.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}