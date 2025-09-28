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
    let mut i: usize = 0;
    let mut found = false;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            found == exists|j: int| 0 <= j < i && v@[j] != 0.0f32,
            !found == forall|j: int| 0 <= j < i ==> v@[j] == 0.0f32,
        decreases v.len() - i
    {
        if v[i] != 0.0f32 {
            found = true;
            proof {
                assert(v@[i as int] != 0.0f32);
                assert(exists|j: int| 0 <= j < v@.len() && v@[j] != 0.0f32);
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