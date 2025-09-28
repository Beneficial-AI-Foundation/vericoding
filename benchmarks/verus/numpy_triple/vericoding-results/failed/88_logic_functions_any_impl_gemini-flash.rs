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
    /* code modified by LLM (iteration 5): Removed `as int` cast from `v@.index(i as int)` since `i` is already `usize`. */
    let mut i: usize = 0;
    let mut found_nonzero = false;

    while i < v.len()
        invariant
            0 <= i as int,
            i as int <= v.len() as int,
            found_nonzero == (exists|j: int| 0 <= j && j < i as int && v@.index(j) != 0.0f32)
    {
        if v@.index(i) != 0.0f32 {
            found_nonzero = true;
            break;
        }
        i = i + 1;
    }
    found_nonzero
}
// </vc-code>

}
fn main() {}