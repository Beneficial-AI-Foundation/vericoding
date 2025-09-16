// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate for element below threshold */
spec fn is_below(x: i32, t: i32) -> bool { x < t }
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate over slice using runtime indexing and maintain spec invariant */
    let mut i: usize = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            forall|j: int| 0 <= j < i as int ==> l@[j] < t,
        decreases l.len() - i
    {
        if !(l[i] < t) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}