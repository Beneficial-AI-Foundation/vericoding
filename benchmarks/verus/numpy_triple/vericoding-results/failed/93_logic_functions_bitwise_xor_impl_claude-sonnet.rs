// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added int parameter type to match sequence indexing */
fn lemma_xor_properties(a: int, b: int)
    requires
        0 <= a <= 255,
        0 <= b <= 255,
    ensures
        a == 0 ==> (a ^ b) == b,
        b == 0 ==> (a ^ b) == a,
        a == b ==> (a ^ b) == 0,
{
}
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == (x1@[i] ^ x2@[i]),
        forall|i: int| 0 <= i < result.len() && x1@[i] == 0 ==> result@[i] == x2@[i],
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast sequence elements to int for lemma call */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == 0,
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let xor_val = x1[i] ^ x2[i];
        proof {
            lemma_xor_properties(x1@[i as int] as int, x2@[i as int] as int);
        }
        result.push(xor_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}