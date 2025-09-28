// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using the correct path to the float basics lemma */
proof fn lemma_f32_bitwise_eq(x: f32, y: f32)
    ensures (x.to_bits() == y.to_bits()) <==> (x == y),
{
    vstd::float::lemma_float_basics(x, y);
}
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no logic changes, only comment updated as the fix was in the helper */
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j],
        decreases a1.len() - i
    {
        if a1[i].to_bits() != a2[i].to_bits() {
            proof {
                lemma_f32_bitwise_eq(a1@[i as int], a2@[i as int]);
            }
            return false;
        }
        proof {
            lemma_f32_bitwise_eq(a1@[i as int], a2@[i as int]);
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}