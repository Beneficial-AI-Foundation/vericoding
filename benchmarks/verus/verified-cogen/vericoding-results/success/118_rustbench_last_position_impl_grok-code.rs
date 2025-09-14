// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implemented loop to iterate from end to find the last position */
    let mut i: usize = a.len();
    while i > 0
        invariant
            0 < i <= a@.len(),
            forall|k: int| i as int <= k < a@.len() ==> a@[k] != elem,
        decreases i
    {
        i -= 1;
        if a[i] == elem {
            return i;
        }
    }
    // This is unreached due to the requires clause ensuring existence
    unreached()
}
// </vc-code>

}
fn main() {}