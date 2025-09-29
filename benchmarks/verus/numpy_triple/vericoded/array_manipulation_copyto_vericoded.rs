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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = dst;
    let mut i = 0;
    while i < result.len()
        invariant
            i <= result.len(),
            result.len() == src.len(),
            result.len() == mask.len(),
            forall|j: int| 0 <= j < i ==> result[j] == if mask[j] { src[j] } else { dst[j] },
            forall|j: int| i <= j < result.len() ==> result[j] == dst[j],
        decreases result.len() - i
    {
        if mask[i] {
            result.set(i, src[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}