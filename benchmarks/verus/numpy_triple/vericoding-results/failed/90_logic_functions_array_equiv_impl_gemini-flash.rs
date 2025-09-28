// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary helper, as the logic can be directly implemented in `array_equiv` */
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 5): fixed compilation errors by using `self.view()` to access the sequence view for indexing */
    let len: usize = a1.len();
    if len == 0 {
        return true;
    }
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int,
            i <= len,
            forall|j: int| 0 <= j < i as int ==> a1.view()[j] == a2.view()[j],
    {
        if a1.view()[i] != a2.view()[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}