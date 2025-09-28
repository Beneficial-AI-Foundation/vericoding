// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32),
        (a@.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a@.len() && a@[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix int type usage in non-ghost code by using usize */
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> a@[j] != 0.0f32,
        decreases (n - i)
    {
        if a[i] == 0.0f32 {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}