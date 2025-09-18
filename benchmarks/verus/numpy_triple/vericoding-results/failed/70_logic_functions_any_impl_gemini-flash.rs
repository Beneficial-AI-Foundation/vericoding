// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a helper function to assert properties of Seq during iteration. */
spec fn is_all_zero_prefix(s: Seq<f32>, k: int) -> bool {
    forall|j: int| 0 <= j < k ==> s[j] == 0.0f32
}

spec fn has_non_zero_prefix(s: Seq<f32>, k: int) -> bool {
    exists|j: int| 0 <= j < k && s[j] != 0.0f32
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
/* code modified by LLM (iteration 5): Fixed array indexing with @ and used helper functions for invariants. Assertions in proof blocks are added to link conditions. */
{
    let len: usize = v.len();
    if len == 0 {
        return false;
    }

    let mut i: usize = 0;
    let mut found_non_zero: bool = false;

    while i < len
        invariant
            0 <= i as int <= len as int,
            found_non_zero == has_non_zero_prefix(v@, i as int),
            (!found_non_zero) == is_all_zero_prefix(v@, i as int),
        decreases len - i
    {
        if v@[i] != 0.0f32 {
            found_non_zero = true;
            proof {
                assert(exists|k: int| 0 <= k < (i as int + 1) && v@[k] != 0.0f32) by {
                    assert(v@[i as int] != 0.0f32);
                }
            }
            break;
        }
        i = i + 1;
    }

    proof {
        if found_non_zero {
            assert(exists|k: int| 0 <= k < len as int && v@[k] != 0.0f32);
        } else {
            assert(forall|k: int| 0 <= k < len as int ==> v@[k] == 0.0f32) by {
                // This follows from the loop invariant: (!found_non_zero) == is_all_zero_prefix(v@, i as int)
                // at loop termination, if found_non_zero is false, then i must be len.
                // So, all elements from 0 up to len are 0.0f32.
            }
        }
    }

    found_non_zero
}
// </vc-code>

}
fn main() {}