use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn swap(a: &mut Vec<bool>, i: usize, j: usize)
    // pre-conditions-start
    requires
        0 <= i < j < old(a).len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k],
        a.len() == old(a).len(),
        a@.to_multiset() =~~= old(a)@.to_multiset(),
    // post-conditions-end
{
    // TODO: Remove this comment and implement the function body
}

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
{
    // TODO: Remove this comment and implement the function body
}

fn main() {}
}
