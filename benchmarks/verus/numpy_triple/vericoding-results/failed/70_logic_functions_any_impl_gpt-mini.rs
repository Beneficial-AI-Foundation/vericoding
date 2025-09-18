// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicates for zero/nonzero */
spec fn is_zero(x: f32) -> bool { x == 0.0f32 }
spec fn is_nonzero(x: f32) -> bool { x != 0.0f32 }
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
    /* code modified by LLM (iteration 5): loop with nat indices and invariants, increment after check to maintain invariants */
    let len: nat = v.len();
    let mut i: nat = 0;
    let mut found: bool = false;
    while i < len
        invariant i <= len;
        invariant found ==> exists|j: int| 0 <= j && j < i as int && v@[j as nat] != 0.0f32;
        invariant !found ==> forall|j: int| 0 <= j && j < i as int ==> v@[j as nat] == 0.0f32;
        decreases len - i;
    {
        if v[i] != 0.0f32 {
            found = true;
        }
        i = i + 1;
    }
    found
}
// </vc-code>

}
fn main() {}