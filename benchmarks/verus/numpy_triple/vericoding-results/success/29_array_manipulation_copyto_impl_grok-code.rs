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
    /* code modified by LLM (iteration 4): added length equalities to loop invariant to satisfy indexing preconditions */
    let mut result: Vec<T> = Vec::new();
    let mut i = 0;
    while i < dst.len()
        invariant
            0 <= i <= dst.len(),
            result.len() == i,
            src.len() == dst.len(),
            mask.len() == dst.len(),
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == if mask[j] { src[j] } else { dst[j] },
        decreases dst.len() - i
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