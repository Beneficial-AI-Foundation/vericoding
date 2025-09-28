// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub fn lemma_vec_index_eq(a: &Vec<f32>, i: usize)
    requires
        0 <= (i as int) < a@.len(),
    ensures
        a@[i as int] == a[i]
{
}
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32),
        (a@.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a@.len() && a@[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added lemma calls to relate executable and ghost views for proving invariants */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int) <= a@.len(),
            forall |j: int| 0 <= j < (i as int) ==> a@[j] != 0.0f32,
        decreases a@.len() - (i as int),
    {
        if a[i] == 0.0f32 {
            proof {
                lemma_vec_index_eq(&a, i);
                assert(a@[i as int] == 0.0f32);
            }
            return false;
        } else {
            proof {
                lemma_vec_index_eq(&a, i);
                assert(a@[i as int] != 0.0f32);
            }
            i += 1;
        }
    }
    return true;
}
// </vc-code>

}
fn main() {}