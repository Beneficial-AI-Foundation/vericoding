use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut false_end: usize = 0;
    for i in 0..a.len() {
        invariant
            0 <= false_end,
            false_end <= i,
            i <= a.len(),
            forall|g: int| 0 <= g < false_end ==> !a@[g],
            forall|g: int| false_end <= g < i ==> a@[g],
            a@.to_multiset() == old(a)@.to_multiset()
        proof {
            // Invariant maintained: when i increments, the quantified conditions extend
        }
        if !a[i] {
            a.swap(i, false_end);
            false_end += 1;
        }
    }
}
// </vc-code>

fn main() {}
}