// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): added parentheses to assert statements for compilation fix */
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1@.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j])
        decreases x1.len() - i
    {
        proof {
            assert(i < x1@.len());
            assert(i < x2@.len());
        }
        let val = x1[i] ^ x2[i];
        result.push(val);
        i += 1;
        proof {
            let x = x1@[i-1];
            let y = x2@[i-1];
            assert(result@[i-1] == x ^ y);
            if x == 0 {
                assert((x ^ y == y));
            }
            if y == 0 {
                assert((x ^ y == x));
            }
            if x == y {
                assert((x ^ y == 0));
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}