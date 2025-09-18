// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn copyto<T: Copy>(dst: Vec<T>, src: Vec<T>, mask: Vec<bool>) -> (result: Vec<T>)
    requires 
        dst.len() == src.len(),
        dst.len() == mask.len(),
    ensures 
        result.len() == dst.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == if mask[i] { src[i] } else { dst[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix verification error */
    let mut result = Vec::new();
    let n = dst.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == dst.len(),
            n == src.len(),
            n == mask.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == if mask[j] { src[j] } else { dst[j] }
        decreases n - i
    {
        if mask[i] {
            result.push(src[i]);
        } else {
            result.push(dst[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}