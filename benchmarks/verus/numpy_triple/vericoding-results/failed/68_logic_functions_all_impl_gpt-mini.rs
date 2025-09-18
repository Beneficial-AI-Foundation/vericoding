// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide spec predicate for all */
spec fn all_spec(a: Vec<f32>) -> bool { forall|i: int| 0 <= i && i < a.len() ==> a@[i] != 0.0f32 }
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate using nat index and invariant as forall up to i; return false on first zero with proof, otherwise return true with proof */
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len()
        invariant (forall|j: int| 0 <= j && j < (i as int) ==> a@[j] != 0.0f32)
        decreases a.len() - i
    {
        if a@[i as int] == 0.0f32 {
            proof {
                assert(i < a.len());
                assert(a@[i as int] == 0.0f32);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        // invariant yields forall j: 0 <= j < a.len() ==> a[j] != 0.0f32
    }
    true
}
// </vc-code>

}
fn main() {}