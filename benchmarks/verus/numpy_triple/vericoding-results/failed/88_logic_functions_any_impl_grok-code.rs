// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof blocks to establish postconditions */
fn any_rec(v: &Vec<f32>, index: usize) -> (result: bool)
    requires
        0 <= index <= v.len(),
    ensures
        result == true <==> exists |k: int| index <= k < v@.len() && v@[k] != 0.0f32,
        result == false <==> forall |k: int| index <= k < v@.len() ==> v@[k] == 0.0f32,
    decreases v.len() - index
{
    if index == v.len() {
        proof {
            assert(!exists |k: int| index <= k < v@.len() && v@[k] != 0.0f32);
            assert(forall |k: int| index <= k < v@.len() ==> v@[k] == 0.0f32);
        }
        false
    } else {
        if v[index] != 0.0f32 {
            proof {
                assert(exists |k: int| index <= k < v@.len() && v@[k] != 0.0f32);
                assert(!forall |k: int| index <= k < v@.len() ==> v@[k] == 0.0f32);
            }
            true
        } else {
            let rec_result = any_rec(v, index + 1);
            proof {
                assert(rec_result == true <==> exists |k: int| (index + 1) <= k < v@.len() && v@[k] != 0.0f32);
                assert(exists |k: int| index <= k < v@.len() && v@[k] != 0.0f32 <==> exists |k: int| (index + 1) <= k < v@.len() && v@[k] != 0.0f32);
                assert(forall |k: int| index <= k < v@.len() ==> v@[k] == 0.0f32 <==> forall |k: int| (index + 1) <= k < v@.len() ==> v@[k] == 0.0f32);
                assert(rec_result == true <==> exists |k: int| index <= k < v@.len() && v@[k] != 0.0f32);
                assert(rec_result == false <==> forall |k: int| index <= k < v@.len() ==> v@[k] == 0.0f32);
            }
            rec_result
        }
    }
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
{
    /* code modified by LLM (iteration 5): call recursive helper with proof block */
    let result = any_rec(&v, 0);
    proof {
        assert(result == true <==> exists |i: int| 0 <= i < v@.len() && v@[i] != 0.0f32);
        assert(result == false <==> forall |i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32);
        assert(v@.len() == 0 ==> result == false);
        assert(forall |i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false);
        assert(exists |i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true);
        assert(result == true || result == false);
        assert(!(result == true && result == false));
    }
    result
}
// </vc-code>

}
fn main() {}