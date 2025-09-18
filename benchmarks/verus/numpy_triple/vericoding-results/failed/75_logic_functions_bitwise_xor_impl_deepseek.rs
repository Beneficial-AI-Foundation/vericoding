// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add decreases clause helper for loop verification */
proof fn decreases_lemma(n: int, len: int) 
    requires n <= len
    ensures len - n >= 0
{
}

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
/* code modified by LLM (iteration 5): Add decreases clause to loop */
{
    let len = x1.len();
    let mut result = Vec::new();
    let mut n: usize = 0;
    while n < len
        invariant
            n <= len,
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == (x1[i] ^ x2[i]),
            forall|i: int| 0 <= i < n && x1[i] == 0 ==> result[i] == x2[i],
            forall|i: int| 0 <= i < n && x2[i] == 0 ==> result[i] == x1[i],
            forall|i: int| 0 <= i < n && x1[i] == x2[i] ==> result[i] == 0,
        decreases len - n
    {
        decreases_lemma(n as int, len as int);
        result.push(x1[n] ^ x2[n]);
        n = n + 1;
    }
    result
}
// </vc-code>

}
fn main() {}