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
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            forall|j: int| 0 <= j < i ==> l[j] < t,
        decreases l.len() - i
    {
        if l[i] >= t {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}