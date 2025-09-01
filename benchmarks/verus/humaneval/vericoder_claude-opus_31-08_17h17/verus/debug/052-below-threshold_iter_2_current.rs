use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            forall|j: int| 0 <= j < i as int ==> l[j] < t,
    {
        if l[i as int] >= t {
            assert(!(forall|j: int| 0 <= j < l.len() ==> l[j] < t)) by {
                assert(0 <= i as int && i as int < l.len());
                assert(l[i as int] >= t);
                assert(!(l[i as int] < t));
            };
            return false;
        }
        i = i + 1;
    }
    
    assert(i == l.len());
    assert(forall|j: int| 0 <= j < i as int ==> l[j] < t);
    assert(forall|j: int| 0 <= j < l.len() ==> l[j] < t);
    true
}
// </vc-code>

fn main() {}
}