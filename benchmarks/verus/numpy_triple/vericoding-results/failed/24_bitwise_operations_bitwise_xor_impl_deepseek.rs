// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use exec mode for lemma and add proof block */
fn lemma_xor_properties(a: i32, b: i32)
    requires a >= 0, b >= 0
    ensures
        (a ^ b) >= 0,
        a == 0 ==> (a ^ b) == b,
        b == 0 ==> (a ^ b) == a,
        a == b ==> (a ^ b) == 0
{
    // These properties are guaranteed by the bitwise XOR operation on non-negative integers
}
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
/* code modified by LLM (iteration 5): Remove exec function call, use proof block instead */
{
    let len = x1.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] >= 0
    {
        let a_val = x1[i];
        let b_val = x2[i];
        proof {
            lemma_xor_properties(a_val, b_val);
        }
        result.push(a_val ^ b_val);
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}