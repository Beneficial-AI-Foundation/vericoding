// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
{
    let mut result: usize = 0;
    let mut found_first = false;
    
    for i in 0..a.len()
        invariant 
            0 <= result < a.len(),
            found_first ==> !f32_is_nan(a@[result as int]),
            forall|j: int| 0 <= j < i && !f32_is_nan(a@[j]) ==> f32_le(a@[result as int], a@[j]),
            forall|j: int| 0 <= j < i && !f32_is_nan(a@[j]) && f32_le(a@[j], a@[result as int]) && f32_le(a@[result as int], a@[j]) ==> result as int <= j,
    {
        if !a[i].is_nan() {
            if !found_first {
                result = i;
                found_first = true;
            } else {
                if a[i] <= a[result] {
                    if a[result] <= a[i] {
                        // They're equal, keep the smaller index
                        if i < result {
                            result = i;
                        }
                    } else {
                        // a[i] is strictly less than a[result]
                        result = i;
                    }
                }
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}