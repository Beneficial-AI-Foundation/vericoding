// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicates for any-nonzero and all-zero using spec indexing */
spec fn any_nonzero(v: Vec<f32>) -> bool { exists|i: int| 0 <= i < v.len() as int && v[i] != 0.0f32 }
spec fn all_zero(v: Vec<f32>) -> bool { forall|i: int| 0 <= i < v.len() as int ==> v[i] == 0.0f32 }
/* helper modified by LLM (iteration 5): logical relationship between helpers */
proof fn all_zero_implies_not_any_nonzero(v: Vec<f32>)
    ensures all_zero(v) ==> !any_nonzero(v)
{ }
proof fn any_nonzero_implies_not_all_zero(v: Vec<f32>)
    ensures any_nonzero(v) ==> !all_zero(v)
{ }
// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32) &&
        (v.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index typing in proofs, added bridging between exec/spec indexing, and strengthened end-state proofs */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i as int && i as int <= v.len() as int,
            forall|j: int| 0 <= j && j < i as int ==> v@[j] == 0.0f32
        decreases (v.len() as int - i as int)
    {
        if v[i] != 0.0f32 {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < v.len() as int);
                assert(v@[j] == v[i as usize]);
                assert(v@[j] != 0.0f32);
                assert(v[j] == v@[j]);
                assert(v[j] != 0.0f32);
                assert(exists|k: int| k == j && 0 <= k && k < v.len() as int && v[k] != 0.0f32);
            }
            return true;
        } else {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < v.len() as int);
                assert(v[i as usize] == 0.0f32);
                assert(v@[j] == v[i as usize]);
                assert(v@[j] == 0.0f32);
            }
            i += 1;
        }
    }
    proof {
        assert(i as int == v.len() as int);
        assert_forall_by(|j: int| {
            requires 0 <= j && j < v.len() as int
            ensures v[j] == 0.0f32
            {
                assert(j < i as int);
                assert(v@[j] == 0.0f32);
                assert(v[j] == v@[j]);
            }
        });
        assert(!exists|j: int| 0 <= j && j < v.len() as int && v[j] != 0.0f32);
    }
    false
}
// </vc-code>

}
fn main() {}