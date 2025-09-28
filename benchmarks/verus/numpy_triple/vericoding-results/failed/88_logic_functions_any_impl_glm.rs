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
    /* code modified by LLM (iteration 5): fixed logic to break early when found and ensure invariants hold */
    let mut found = false;
    let mut i: usize = 0;
    while i < v.len()
        invariant 
            0 <= i <= v@.len(),
            found ==> exists|j: int| 0 <= j < i && v@[j] != 0.0f32,
            !found ==> forall|j: int| 0 <= j < i ==> v@[j] == 0.0f32,
        decreases v@.len() - i
    {
        if v[i] != 0.0f32 {
            found = true;
            proof {
                assert(v@[i] != 0.0f32);
                assert(i < v@.len());
            }
            break;
        }
        i = i + 1;
    }
    found
}
// </vc-code>

}
fn main() {}