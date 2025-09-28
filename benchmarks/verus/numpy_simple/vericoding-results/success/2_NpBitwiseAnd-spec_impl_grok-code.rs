// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added equality of lengths to loop invariant to prove indexing preconditions */
    if a.len() == 0 {
        return Vec::new();
    }
    let mut result: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] & b[j])
        decreases a.len() - i
    {
        result.push(a[i] & b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}