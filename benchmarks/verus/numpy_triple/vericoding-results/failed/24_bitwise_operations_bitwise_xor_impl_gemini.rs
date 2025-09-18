// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed, proofs are inline */
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
    /* code modified by LLM (iteration 5): fixed bit_vector proofs by extracting spec values to local variables. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|k: int| 0 <= k < x1.len() ==> x1@[k] >= 0,
            forall|k: int| 0 <= k < x2.len() ==> x2@[k] >= 0,
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == x2@[j],
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == x2@[j] ==> result@[j] == 0,
        decreases x1.len() - i
    {
        let val = x1[i] ^ x2[i];
        proof {
            let x1_i = x1@[i as int];
            let x2_i = x2@[i as int];

            assert(x1_i >= 0 && x2_i >= 0);
            assert((x1_i ^ x2_i) >= 0) by(bit_vector);

            if x1_i == 0 {
                assert((x1_i ^ x2_i) == x2_i) by(bit_vector);
            }
            if x2_i == 0 {
                assert((x1_i ^ x2_i) == x1_i) by(bit_vector);
            }
            if x1_i == x2_i {
                assert((x1_i ^ x2_i) == 0) by(bit_vector);
            }

            assert(val == (x1_i ^ x2_i));
        }
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}