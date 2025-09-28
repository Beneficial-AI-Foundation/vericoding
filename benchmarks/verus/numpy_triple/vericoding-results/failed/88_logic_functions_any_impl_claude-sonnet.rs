// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed syntax error in assert statement by separating conditions */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] == 0.0f32,
        decreases v.len() - i
    {
        if v[i] != 0.0f32 {
            proof {
                assert(0 <= i as int);
                assert(i as int < v@.len());
                assert(v@[i] != 0.0f32);
                assert(exists|k: int| 0 <= k < v@.len() && v@[k] != 0.0f32);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        assert(i == v.len());
        assert(forall|j: int| 0 <= j < v@.len() ==> v@[j] == 0.0f32);
    }
    false
}
// </vc-code>

}
fn main() {}