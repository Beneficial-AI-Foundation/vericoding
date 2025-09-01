use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty, no updates needed
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
    let len = a.len();
    let mut false_region: usize = 0;
    let mut j: usize = 0;
    while j < len
        invariant
            a@.len() == old(a)@.len(),
            0 <= false_region <= j <= len,
            forall |k: int| 0 <= k < (false_region as int) ==> #[trigger] (a@[k] == false),
            forall |k: int| (false_region as int) <= k < (j as int) ==> #[trigger] (a@[k] == true),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        if a[j] == false {
            a.swap(false_region, j);
            false_region = false_region.add(1);
        }
        j = j.add(1);
    }
}
// </vc-code>

fn main() {}
}