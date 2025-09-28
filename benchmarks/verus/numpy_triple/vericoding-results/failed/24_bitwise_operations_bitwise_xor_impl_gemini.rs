// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed `by(bit_vector)` which fails for `i32` */
proof fn bitwise_xor_properties(a: i32, b: i32)
    requires
        a >= 0,
        b >= 0,
    ensures
        a ^ b >= 0,
        (a == 0) ==> (a ^ b == b),
        (b == 0) ==> (a ^ b == a),
        (a == b) ==> (a ^ b == 0),
{
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
{
    /* code modified by LLM (iteration 5): added function preconditions to loop invariant and fixed proof call */
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
        let r = x1[i] ^ x2[i];
        proof {
            bitwise_xor_properties(x1@[i as int], x2@[i as int]);
        }
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}