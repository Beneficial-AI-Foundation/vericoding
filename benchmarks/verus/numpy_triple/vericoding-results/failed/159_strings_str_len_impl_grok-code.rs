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
/* code modified by LLM (iteration 5): fixed compilation errors by using a@.len() for Seq::new length and a@[i].spec_len() as nat in lambda */
{
    let len = a@.len();
    let seq_result = Seq::new(len, |i: int| a@[i].spec_len() as nat);
    seq_result.to_vec()
}
// </vc-code>

}
fn main() {}