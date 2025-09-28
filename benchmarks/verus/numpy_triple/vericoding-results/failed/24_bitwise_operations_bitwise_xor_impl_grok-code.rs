// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed .index(i) to [i] for vector indexing to fix compilation error due to Index trait not in scope */
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] ^ x2[j],
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            i <= n,
        decreases n - i
    {
        let val = ((x1[i] as u32) ^ (x2[i] as u32)) as i32;
        result.push(val);
        proof {
            assert(val >= 0);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}