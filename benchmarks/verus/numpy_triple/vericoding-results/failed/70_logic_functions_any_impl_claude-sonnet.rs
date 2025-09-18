// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Enhanced helper lemma with proof implementation */
proof fn lemma_any_postcondition(v: Vec<f32>, result: bool, found_nonzero: bool, last_index: int)
    requires
        last_index == v.len(),
        result == found_nonzero,
        found_nonzero <==> exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32,
        !found_nonzero ==> forall|j: int| 0 <= j < last_index ==> v[j] == 0.0f32
    ensures
        (result == true <==> exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32)
{
    if result {
        assert(found_nonzero);
        assert(exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32);
    } else {
        assert(!found_nonzero);
        assert(forall|j: int| 0 <= j < v.len() ==> v[j] == 0.0f32);
    }
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
    /* code modified by LLM (iteration 5): Fixed syntax error with assert statement */
    let mut found_nonzero = false;
    
    for i in 0..v.len()
        invariant
            found_nonzero <==> exists|j: int| 0 <= j < i && v[j] != 0.0f32,
            !found_nonzero ==> forall|j: int| 0 <= j < i ==> v[j] == 0.0f32
    {
        if v[i] != 0.0f32 {
            found_nonzero = true;
            proof {
                assert(v[i as int] != 0.0f32);
                assert(0 <= i as int && i as int < v.len());
                assert(exists|j: int| 0 <= j < v.len() && v[j] != 0.0f32) by {
                    assert(v[i as int] != 0.0f32);
                };
            }
            return true;
        }
    }
    
    proof {
        assert(!found_nonzero);
        assert(forall|j: int| 0 <= j < v.len() ==> v[j] == 0.0f32) by {
            assert(forall|j: int| 0 <= j < v.len() ==> v[j] == 0.0f32);
        };
        lemma_any_postcondition(v, false, found_nonzero, v.len() as int);
    }
    
    false
}
// </vc-code>

}
fn main() {}