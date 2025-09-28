// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed once again */
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
/* code modified by LLM (iteration 5): The `break` assertion is now valid. Fixed remaining invariant issues. */
{
    let mut i: usize = 0;
    let mut result = true;

    while i < a.len()
        invariant 
            0 <= i,
            i <= a.len(),
            result == (forall|j: int| 0 <= j < i ==> a@[j] != 0.0f32),
            (result == false ==> exists|k: int| 0 <= k < i && a@[k] == 0.0f32),

        decreases a.len() - i
    {
        if a[i] == 0.0f32 {
            result = false;
            proof {
                assert(exists|k: int| 0 <= k < (i as int) + 1 && a@[k] == 0.0f32);
            }
            break;
        }
        i = i + 1;
    }

    // Proof to connect loop invariant to postcondition when loop finishes normally (result is true)
    proof {
        if result {
            assert(forall|j: int| 0 <= j < a.len() ==> a@[j] != 0.0f32) by {
                if a.len() > 0 {
                    assert(i == a.len());
                    assert(forall|j: int| 0 <= j < i ==> a@[j] != 0.0f32);
                } else {
                    assert(i == 0);
                }
            };
        } else {
            assert(exists|k: int| 0 <= k < a.len() && a@[k] == 0.0f32) by {
                assert(exists|k: int| 0 <= k < i && a@[k] == 0.0f32);
                assert(i <= a.len());
            };
        }
    }

    result
}
// </vc-code>

}
fn main() {}