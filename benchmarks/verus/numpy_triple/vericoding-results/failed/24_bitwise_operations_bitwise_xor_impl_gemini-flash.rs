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
/* code modified by LLM (iteration 5): Fix type mismatch in `Seq::index` and use `spec_bitxor` for bitwise XOR. */
{
    let mut result: Vec<i32> = Vec::new();
    let len = x1.len();

    let x1_spec = x1.view();
    let x2_spec = x2.view();

    if len > 0 {
        proof {
            assert forall|i: int| 0 <= i < len implies x1_spec.index(i) >= 0 by { };
            assert forall|i: int| 0 <= i < len implies x2_spec.index(i) >= 0 by { };
        }
    }

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            result.len() == i,
            result.view().len() == i as nat,
            forall|j: int| 0 <= j < i ==> result.view().index(j) == (x1_spec.index(j) ^ x2_spec.index(j)),
            forall|j: int| 0 <= j < i ==> result.view().index(j) >= 0,
            forall|j: int| 0 <= j < i && x1_spec.index(j) == 0 ==> result.view().index(j) == x2_spec.index(j),
            forall|j: int| 0 <= j < i && x2_spec.index(j) == 0 ==> result.view().index(j) == x1_spec.index(j),
            forall|j: int| 0 <= j < i && x1_spec.index(j) == x2_spec.index(j) ==> result.view().index(j) == 0,
    {
        let val1 = x1[i];
        let val2 = x2[i];
        let xor_val = val1 ^ val2;
        result.push(xor_val);

        proof {
            assert(result.view().index(i as int) == (x1_spec.index(i as int) ^ x2_spec.index(i as int)));

            assert(val1 >= 0 && val2 >= 0);
            assert(xor_val >= 0) by(bit_vector) { assert((val1 as int).spec_bitxor(val2 as int) == xor_val as int) };

            if val1 == 0 {
                assert(xor_val == (0 ^ val2));
                assert(xor_val == val2);
            }

            if val2 == 0 {
                assert(xor_val == (val1 ^ 0));
                assert(xor_val == val1);
            }

            if val1 == val2 {
                assert(val1 ^ val1 == 0);
                assert(xor_val == 0);
            }
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}