// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed assert from helper section as it is not a helper but a verification tool for lemmas/proofs */
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the requires conditions for the bitvector assertions. They must refer to the values directly (x1[i] and x2[i]), not the local variables val1 and val2 because the requires clause applies to the state before the assert statement executes. Also added the `x1[i] >= 0` and `x2[i] >= 0` to the loop invariant so the bit_vector asserts are satisfied. */
{
    let mut result: Vec<i32> = Vec::new();
    let len = x1.len();
    
    for i in 0..len
        invariant 
            0 <= i as int <= len as int,
            result.len() == i as nat,
            x1.len() == len,
            x2.len() == len,
            forall|j: int| 0 <= j < result.len() ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < result.len() ==> result[j] >= 0,
            forall|j: int| 0 <= j < result.len() ==> result[j] <= x1[j],
            forall|j: int| 0 <= j < result.len() ==> result[j] <= x2[j],
            forall|j: int| 0 <= j < result.len() ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < result.len() ==> (x1[j] == x2[j] ==> result[j] == x1[j]),
            0 <= i < x1.len(),
            0 <= i < x2.len(),
            x1[i] >= 0,
            x2[i] >= 0,

    {
        let val1 = x1[i];
        let val2 = x2[i];
        let and_val = val1 & val2;

        proof {
            assert(and_val == (x1[i as int] & x2[i as int]));
            assert(and_val >= 0) by (bit_vector) requires x1[i] >= 0, x2[i] >= 0;
            assert (and_val <= val1) by (bit_vector) requires x1[i] >= 0, x2[i] >= 0;
            assert (and_val <= val2) by (bit_vector) requires x1[i] >= 0, x2[i] >= 0;
            assert (and_val == 0 <==> (val1 == 0 || val2 == 0)) by (bit_vector) requires x1[i] >= 0, x2[i] >= 0;
            assert (val1 == val2 ==> and_val == val1) by (bit_vector) requires x1[i] >= 0, x2[i] >= 0;
        }

        result.push(and_val);
    }
    result
}
// </vc-code>

}
fn main() {}