// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed vec_sum_lemma syntax with proper body */
uninterp spec fn vec_sum(a: Seq<f32>) -> f32;

spec fn vec_sum_lemma(a: Seq<f32>, i: int) -> f32
    decreases a.len() - i
{
    if i == a.len() {
        0.0f32
    } else {
        a[i] + vec_sum_lemma(a, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed invalid requires clause from previous version */
{
    let mut sum = 0.0f32;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == vec_sum_lemma(a@, 0) - vec_sum_lemma(a@, i)
    {
        proof {
            // Show that sum + a[i] equals the lemma result for the next iteration
            assert(sum + a[i] == vec_sum_lemma(a@, 0) - vec_sum_lemma(a@, i + 1)) by {
                // Use algebraic properties to prove the invariant maintains
                assert(vec_sum_lemma(a@, i) == a[i] + vec_sum_lemma(a@, i + 1));
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    proof {
        // Final proof that sum equals vec_sum(a@)
        assert(vec_sum_lemma(a@, a.len()) == 0.0f32);
        assert(sum == vec_sum_lemma(a@, 0) - vec_sum_lemma(a@, a.len()));
    }
    
    sum
}
// </vc-code>

}
fn main() {}