// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Corrected syntax to use assert with by(bit_vector). */
proof fn bitwise_not_equivalence(x: i32)
    ensures !x == -(x + 1)
{
    assert(!x == -(x + 1)) by(bit_vector);
}
// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == -(x[i] + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Used a proof block to call the helper lemma from exec code. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1),
        decreases x.len() - i,
    {
        let val = x[i];
        let inverted_val = !val;
        proof {
            bitwise_not_equivalence(val);
        }
        result.push(inverted_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}