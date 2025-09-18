// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof block from proof function */
spec fn xor_nonnegative(a: i32, b: i32) -> bool {
    a >= 0 && b >= 0 ==> (a ^ b) >= 0
}

proof fn xor_properties_lemma(a: i32, b: i32)
    requires a >= 0 && b >= 0
    ensures
        (a ^ b) >= 0,
        a == 0 ==> (a ^ b) == b,
        b == 0 ==> (a ^ b) == a,
        a == b ==> (a ^ b) == 0
{
    // XOR properties are built into the SMT solver
    // For non-negative integers, XOR result is non-negative
    assert(a >= 0 && b >= 0);
    // XOR with zero gives the other operand
    if a == 0 {
        assert((a ^ b) == b);
    }
    if b == 0 {
        assert((a ^ b) == a);
    }
    // XOR of identical values is zero
    if a == b {
        assert((a ^ b) == 0);
    }
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
/* code modified by LLM (iteration 5): fixed proof block placement */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == 0
        decreases x1.len() - i
    {
        proof {
            assert(i < x1.len());
            assert(i < x2.len());
            assert(x1@[i as int] >= 0);
            assert(x2@[i as int] >= 0);
        }
        xor_properties_lemma(x1[i], x2[i]);
        let xor_value = x1[i] ^ x2[i];
        result.push(xor_value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}