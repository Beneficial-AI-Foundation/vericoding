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
    /* code modified by LLM (iteration 5): added length equalities to loop invariant and removed redundant assertions */
    let mut result = Vec::with_capacity(dst.len());
    let mut i: usize = 0;
    while i < dst.len()
        invariant
            dst.len() == src.len(),
            dst.len() == mask.len(),
            i <= dst.len(),
            i <= src.len(),
            i <= mask.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                j < src.len() && j < mask.len() &&
                #[trigger] result@[j] == (if mask@[j] { src@[j] } else { dst@[j] })
        decreases dst.len() - i
    {
        if mask[i] {
            result.push(src[i]);
        } else {
            result.push(dst[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}