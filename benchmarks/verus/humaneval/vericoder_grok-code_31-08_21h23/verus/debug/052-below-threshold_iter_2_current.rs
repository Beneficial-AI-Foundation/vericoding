use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let len = l.len();
    while i < len
        invariant
            forall|j: int| 0 <= j < i ==> l[j] < t,
        invariant
            i <= len,
    {
        if l[i] >= t {
            return false;
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < l.len() ==> l[j] < t);
    true
}
// </vc-code>

fn main() {}
}