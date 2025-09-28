// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple usize-to-int bounds lemma */
proof fn lemma_usize_int_bounds(i: usize, n: usize)
    ensures
        0 <= i as int,
        0 <= n as int,
        (i < n) ==> (i as int) < (n as int),
{}
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
    /* code modified by LLM (iteration 5): straightforward loop building result and maintaining elementwise XOR relation */
    let n = x1.len();
    let mut result: Vec<i32> = Vec::new();
    while result.len() < n
        invariant
            n == x1.len(),
            n == x2.len(),
            result.len() <= n,
            forall|j: int| 0 <= j < result.len() as int ==> result@[j] == (x1@[j] ^ x2@[j]),
        decreases n as int - result.len() as int
    {
        let i = result.len();
        let a = x1[i];
        let b = x2[i];
        let r = a ^ b;
        result.push(r);
        proof {
            let j = i as int;
            assert(a == x1@[j]);
            assert(b == x2@[j]);
            assert(result@[j] == r);
            assert(result@[j] == (x1@[j] ^ x2@[j]));
        }
    }
    result
}
// </vc-code>

}
fn main() {}