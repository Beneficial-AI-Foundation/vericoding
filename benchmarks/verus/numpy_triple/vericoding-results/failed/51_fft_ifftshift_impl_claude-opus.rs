// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let n = x.len();
    let mid = n / 2;
    let mut result: Vec<f32> = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x[((j + mid as int) % n as int) as int],
        decreases n - i
    {
        let shifted_idx = (i + mid) % n;
        result.push(x[shifted_idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}