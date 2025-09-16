// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed compilation error by using l[i] for execution access instead of l@[i as int] */
    let mut i: usize = 0;
    while i < l.len()
        invariant
            forall|j: int| 0 <= j < i ==> l@[j] < t,
            i <= l.len(),
        decreases l.len() - i
    {
        if l[i] >= t {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}