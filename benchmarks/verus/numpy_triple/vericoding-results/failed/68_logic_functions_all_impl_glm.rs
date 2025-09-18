// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant syntax */
{
    if a.len() == 0 {
        true
    } else {
        let n = a.len();
        let mut i = 0;
        while i < n
            invariant { 0 <= i <= n }
            invariant { forall|j: int| 0 <= j < i ==> a[j] != 0.0f32 }
        {
            if a[i] == 0.0f32 {
                return false;
            }
            i += 1;
        }
        true
    }
}
// </vc-code>

}
fn main() {}