// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
spec fn all_zero_prefix(s: Seq<f32>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> s[i] == 0.0f32
}

proof fn all_zero_prefix_extend(s: Seq<f32>, i: int)
    requires
        0 <= i < s.len(),
        all_zero_prefix(s, i),
        s[i] == 0.0f32,
    ensures
        all_zero_prefix(s, i + 1)
{
}
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
    /* code modified by LLM (iteration 5): fixed compilation errors by using v[i] for indexing in proof contexts */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            all_zero_prefix(v.view(), i as int),
        decreases v.len() - i
    {
        if v[i] != 0.0f32 {
            proof {
                assert(v[i as int] != 0.0f32);
                assert(exists|j: int| 0 <= j < v.len() && v[j] != 0.0f32);
                assert(!(forall|j: int| 0 <= j < v.len() ==> v[j] == 0.0f32));
            }
            return true;
        } else {
            proof {
                all_zero_prefix_extend(v.view(), i as int);
            }
            i = i + 1;
        }
    }
    
    proof {
        assert(all_zero_prefix(v.view(), v.len() as int));
        if exists|j: int| 0 <= j < v.len() && v[j] != 0.0f32 {
            let j = choose |j: int| 0 <= j < v.len() && v[j] != 0.0f32;
            assert(v[j] == 0.0f32); // From all_zero_prefix
            assert(false);
        }
    }
    return false;
}
// </vc-code>

}
fn main() {}