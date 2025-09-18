// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed helper lemma with correct logical equivalence proof */
proof fn all_elements_nonzero_equiv(a: Vec<f32>, result: bool)
    requires
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32)
    ensures
        (exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true
{
    if exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32 {
        assert(!(forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32));
        assert(result == false);
    }
    if forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32 {
        assert(result == true);
    }
}
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
    /* code modified by LLM (iteration 5): Fixed ghost type usage by using usize index directly */
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a[j] != 0.0f32
    {
        if a[i] == 0.0f32 {
            proof {
                assert(exists|k: int| 0 <= k < a.len() && a[k] == 0.0f32);
                all_elements_nonzero_equiv(a, false);
            }
            return false;
        }
        proof {
            assert(a[i as int] != 0.0f32);
        }
    }
    proof {
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] != 0.0f32);
        all_elements_nonzero_equiv(a, true);
    }
    true
}
// </vc-code>

}
fn main() {}