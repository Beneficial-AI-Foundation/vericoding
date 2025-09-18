// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): corrected the lemma name from `lemma_len_zero_is_empty` to `lemma_len_is_zero_is_empty` */
{
    let result = Vec::from_seq(a@.map(|s: String| s@.len()));

    proof {
        assert forall|i: int| 0 <= i < a.len() implies (a[i as usize]@.len() == 0 <==> a[i as usize]@ == Seq::<char>::empty()) by {
            vstd::seq::lemma_len_is_zero_is_empty::<char>(a[i as usize]@);
        }
    }

    result
}
// </vc-code>

}
fn main() {}