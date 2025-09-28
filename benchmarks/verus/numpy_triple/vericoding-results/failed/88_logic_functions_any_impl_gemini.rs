// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Seq indexing from s@[] to s[] to resolve compilation errors. */
proof fn lemma_forall_extend(s: Seq<f32>, i: int)
    requires
        0 <= i < s.len(),
        forall|j: int| 0 <= j < i ==> s[j] == 0.0f32,
        s[i] == 0.0f32,
    ensures
        forall|j: int| 0 <= j < i + 1 ==> s[j] == 0.0f32,
{
}
// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32) &&
        (v@.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No logical changes; the implementation was correct but failed due to a compilation error in the helper function. */
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < (i as int) ==> v@[j] == 0.0f32,
        decreases v.len() - i
    {
        if v[i] != 0.0f32 {
            assert(exists|k: int| 0 <= k < v@.len() && v@[k] != 0.0f32);
            return true;
        }

        proof {
            lemma_forall_extend(v@, i as int);
        }

        i = i + 1;
    }

    assert(forall|j: int| 0 <= j < v@.len() ==> v@[j] == 0.0f32);
    return false;
}
// </vc-code>

}
fn main() {}