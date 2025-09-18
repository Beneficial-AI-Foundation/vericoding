// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<u32>, x2: Vec<u32>) -> (result: Vec<u32>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed indexing to use runtime Vec indexing instead of sequence view */
{
    let mut result: Vec<u32> = Vec::new();
    let len = x1.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == x1@.len(),
            len == x2@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] ^ x2@[j],
    {
        result.push(x1[i] ^ x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}