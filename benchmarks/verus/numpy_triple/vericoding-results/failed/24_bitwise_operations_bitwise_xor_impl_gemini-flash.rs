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
/* code modified by LLM (iteration 4): Added decreases clause. */
{
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i,
            i <= x1.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j < i ==> result_vec[j] >= 0,
        decreases x1.len() - i
    {
        let xor_val = x1[i] ^ x2[i];
        result_vec.push(xor_val);
        proof {
            let k = i as int;
            assert(x1@[k] >= 0);
            assert(x2@[k] >= 0);
            assert(result_vec@[k] == (x1@[k] ^ x2@[k]));
            assert(xor_val >= 0) by(bit_vector);
            assert(result_vec@[k] >= 0);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}