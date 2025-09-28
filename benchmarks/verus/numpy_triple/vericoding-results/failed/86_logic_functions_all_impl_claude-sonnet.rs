// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper to verify element access properties */
fn element_at_index(a: &Vec<f32>, idx: usize) -> (val: f32)
    requires
        idx < a@.len(),
    ensures
        val == a@[idx as int],
{
    a[idx]
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
    /* code modified by LLM (iteration 5): use helper function for safe element access */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] != 0.0f32,
        decreases a@.len() - i
    {
        let val = element_at_index(&a, i);
        if val == 0.0f32 {
            proof {
                assert(val == a@[i as int]);
                assert(a@[i as int] == 0.0f32);
                assert(0 <= i < a@.len());
                assert(exists|k: int| 0 <= k < a@.len() && a@[k] == 0.0f32) by {
                    assert(0 <= i < a@.len() && a@[i as int] == 0.0f32);
                }
            }
            return false;
        }
        proof {
            assert(val == a@[i as int]);
            assert(a@[i as int] != 0.0f32);
            assert(forall|j: int| 0 <= j < i + 1 ==> a@[j] != 0.0f32) by {
                assert(forall|j: int| 0 <= j < i ==> a@[j] != 0.0f32);
                assert(a@[i as int] != 0.0f32);
            }
        }
        i = i + 1;
    }
    proof {
        assert(i == a@.len());
        assert(forall|j: int| 0 <= j < a@.len() ==> a@[j] != 0.0f32);
    }
    true
}
// </vc-code>

}
fn main() {}