// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No additional helper needed for this implementation. */

/* No additional helpers required as the function can be implemented directly. */

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
/* code modified by LLM (iteration 5): Implement any() by iterating through vector with proof blocks to link code conditions to spec invariants for correct verification. */
{
    let mut result = false;
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            result ==> (exists|j: int| 0 <= j < i && v@[j] != 0.0f32),
            !result ==> (forall|j: int| 0 <= j < i ==> v@[j] == 0.0f32)
        decreases v.len() - i
    {
        if v[i] != 0.0f32 {
            proof {
                assert(v@[i] != 0.0f32);
                assert(exists|j: int| 0 <= j < i + 1 && v@[j] != 0.0f32);
            }
            result = true;
        } else {
            proof {
                assert(v@[i] == 0.0f32);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}