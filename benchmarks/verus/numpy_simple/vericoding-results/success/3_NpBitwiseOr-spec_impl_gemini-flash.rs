// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_or(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as u32 == (a[i] as u32 | b[i] as u32),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Access a and b directly within the loop using current index */
{
    let n = a.len();
    let mut result_vec = Vec::<u8>::new();
    while result_vec.len() < n
        invariant
            result_vec.len() <= n,
            a.len() == n,
            b.len() == n,
            forall|k: int| 0 <= k < result_vec.len() ==> result_vec[k] as u32 == (a[k as int] as u32 | b[k as int] as u32),
        decreases n - result_vec.len()
    {
        let i: usize = result_vec.len();
        result_vec.push(a[i] | b[i]);
    }
    result_vec
}
// </vc-code>


}
fn main() {}