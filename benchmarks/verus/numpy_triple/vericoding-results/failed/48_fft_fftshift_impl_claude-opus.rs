// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow by converting to int before operations */
    let n = x.len();
    let mut result = Vec::new();
    let shift = n / 2;
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[((j + n as int - shift as int) % n as int) as int],
        decreases n - i
    {
        let new_idx = (((i as int + n as int - shift as int) % n as int) as usize);
        result.push(x[new_idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}