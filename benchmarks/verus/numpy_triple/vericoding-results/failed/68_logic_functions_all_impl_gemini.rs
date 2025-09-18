// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added proof blocks for loop invariant and postcondition */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] != 0.0f32,
        decreases a.len() - i
    {
        if a[i] == 0.0f32 {
            proof {
                assert(exists|k: int| 0 <= k < a.len() && a@[k] == 0.0f32) by {
                    reveal_with_witness(i as int);
                };
            }
            return false;
        } else {
            proof {
                assert forall|j: int| 0 <= j < (i + 1) as int implies a@[j] != 0.0f32 by {
                    if j < i {
                        // This case is covered by the loop invariant
                    } else {
                        // This case (j == i) is covered by the `else` branch condition
                        assert(a@[j] != 0.0f32);
                    }
                }
            }
            i = i + 1;
        }
    }
    true
}
// </vc-code>

}
fn main() {}