// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `array_equiv_spec` to use `@` for sequence indexing. */
spec fn array_equiv_spec(a1: Seq<f32>, a2: Seq<f32>) -> bool { forall|i: int| 0 <= i < a1.len() ==> a1@[i] == a2@[i] }
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors related to `to_seq()` method not existing by using `seq_from_slice()` and corrected `array_equiv_spec` call to pass `Seq<f32>` instead of `&Seq<f32>`. */
{
    if a1.len() != a2.len() {
        return false;
    }

    let a1_seq = Seq::seq_from_slice(&a1);
    let a2_seq = Seq::seq_from_slice(&a2);

    let mut i: usize = 0;
    while (i < a1.len())
        invariant
            0 <= i as int <= a1.len() as int,
            forall|j: int| 0 <= j < i as int ==> a1_seq@[j] == a2_seq@[j]
    {
        if a1[i] != a2[i] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(array_equiv_spec(a1_seq, a2_seq));
    }
    true
}
// </vc-code>

}
fn main() {}